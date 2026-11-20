-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.copyW_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:34:42.687987+00:00
-- url     : https://prove2.me/submissions/e9651102-2f3f-42c8-995e-b4057b23fd78

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000
import Theorems.Thm_EditMulticoloring_Dev_Ram_kappa_bits_le

section
-- module Solutions.EditMulticoloring.RamLib
attribute [-simp] _root_.EditMulticoloring.Dev.Ram.arith_xor
/-!
# Program-proof library for `Cmd` (q379, Part L)

* `simp` lemmas for `Cmd.exec` / `Cmd.cost` of every constructor and convenience constructor;
* `HS.setR` (register update) and `HS.arr` lemmas;
* syntactic frames: `Cmd.wregs` (registers possibly written), `Cmd.reads`, `Cmd.emits`, `Cmd.stores`;
* monotonicity of `kappa` and `RAM.bits`;
* the general loop lemma `loop_spec`, the counted for-loop `forLoop` with `forLoop_spec`
  (invariant + cost) and its list-fold form `forLoop_fold`;
* `copyW`, a word copy between (array, offset) places.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ## States -/

/-! ## Small rewriting helpers (use with `simp (disch := omega)`) -/

/-! ## `exec` and `cost` of the constructors -/

section ExecCost
variable (inp : ℕ → ℕ) (B : ℕ)

theorem exec_loop (a : ℕ) (c : Cmd) (s : HS) :
    (Cmd.loop a c).exec inp s = (c.exec inp)^[s.regs a] s := rfl

end ExecCost

/-! ## Monotonicity of the charges -/

theorem kappa_mono {B B' W W' : ℕ} (hB : B ≤ B') (hW : W ≤ W') : kappa B W ≤ kappa B' W' := by
  unfold kappa
  have : (W + 2) ^ 2 ≤ (W' + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  omega

theorem kappa_mono_right (B : ℕ) {W W' : ℕ} (hW : W ≤ W') : kappa B W ≤ kappa B W' :=
  kappa_mono le_rfl hW

theorem kappa_zero_le (B M : ℕ) : kappa B 0 ≤ kappa B (RAM.bits M) :=
  kappa_mono_right B (Nat.zero_le _)

/-! ## Syntactic frames -/

/-! ## Loops -/

section Loops
variable (inp : ℕ → ℕ) (B : ℕ)

/-- `loop a c`, with an invariant indexed by the number of completed iterations, and a
per-iteration cost bound. -/
theorem loop_spec (a : ℕ) (c : Cmd) (s : HS) (P : ℕ → HS → Prop) (C : ℕ → ℕ)
    (h0 : P 0 s)
    (hstep : ∀ k < s.regs a, ∀ st, P k st → P (k + 1) (c.exec inp st) ∧ c.cost inp B st ≤ C k) :
    P (s.regs a) ((Cmd.loop a c).exec inp s) ∧
    (Cmd.loop a c).cost inp B s ≤
      (s.regs a + 2) * kappa B (RAM.bits (s.regs a)) + ∑ k ∈ Finset.range (s.regs a), C k := by
  set N := s.regs a with hN
  have key : ∀ v k st, k + v = N → P k st →
      P N ((c.exec inp)^[v] st) ∧
      loopCost B (c.exec inp) (c.cost inp B) v st ≤
        (v + 1) * kappa B (RAM.bits N) + ∑ j ∈ Finset.range v, C (k + j) := by
    intro v
    induction v with
    | zero =>
      intro k st hk hP
      simp only [Nat.add_zero] at hk
      subst hk
      refine ⟨hP, ?_⟩
      simp only [loopCost, Finset.range_zero, Finset.sum_empty, zero_add, one_mul, add_zero]
      exact kappa_zero_le B _
    | succ v ih =>
      intro k st hk hP
      have hkN : k < N := by omega
      obtain ⟨hP1, hc⟩ := hstep k hkN st hP
      obtain ⟨hP2, hc2⟩ := ih (k + 1) (c.exec inp st) (by omega) hP1
      refine ⟨by rw [Function.iterate_succ_apply]; exact hP2, ?_⟩
      simp only [loopCost]
      have hκ : kappa B (RAM.bits (v + 1)) ≤ kappa B (RAM.bits N) := kappa_bits_le B (by omega)
      rw [Finset.sum_range_succ']
      have : ∑ j ∈ Finset.range v, C (k + 1 + j) = ∑ j ∈ Finset.range v, C (k + (j + 1)) := by
        apply Finset.sum_congr rfl; intro j _; congr 1; omega
      rw [this] at hc2
      simp only [Nat.add_zero] at *
      nlinarith
  obtain ⟨h1, h2⟩ := key N 0 s (by omega) h0
  refine ⟨by rw [exec_loop]; exact h1, ?_⟩
  simp only [Cmd.cost]
  simp only [zero_add] at h2
  rw [← hN]
  nlinarith

/-- The for-loop lemma: invariant `P k` after `k` iterations (the counter register `i` holds
`k` at the start of iteration `k`, the body must keep it), and cost. -/
theorem forLoop_spec (i n one : ℕ) (body : Cmd) (s : HS) (hni : n ≠ i) (hio : i ≠ one)
    (P : ℕ → HS → Prop) (C : ℕ → ℕ)
    (h0 : P 0 (s.setR i 0))
    (hstep : ∀ k < s.regs n, ∀ st, P k st → st.regs i = k →
      (body.exec inp st).regs i = k ∧
      P (k + 1) (((body.exec inp st).setR one 1).setR i (k + 1)) ∧
      body.cost inp B st ≤ C k) :
    P (s.regs n) ((forLoop i n one body).exec inp s) ∧
    (forLoop i n one body).cost inp B s ≤
      3 * (s.regs n + 1) * kappa B (RAM.bits (s.regs n)) + ∑ k ∈ Finset.range (s.regs n), C k := by
  set N := s.regs n with hN
  have hN' : (s.setR i 0).regs n = N := by simp [hni, hN]
  have L := loop_spec inp B n (.seq body (.seq (lit one 1) (ar .add i i one))) (s.setR i 0)
    (fun k st => P k st ∧ st.regs i = k) (fun k => C k + 2 * kappa B (RAM.bits N))
    ⟨h0, by simp⟩ (by
      intro k hk st ⟨hP, hi⟩
      rw [hN'] at hk
      obtain ⟨hb1, hb2, hb3⟩ := hstep k hk st hP hi
      have hset : (Function.update (body.exec inp st).regs one 1) i +
          (Function.update (body.exec inp st).regs one 1) one = k + 1 := by
        simp [hio, hb1]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simp only [exec_seq, exec_lit, exec_ar, arith_add, HS.setR_regs]
        rw [hset]; exact hb2
      · simp [hio, hb1]
      · simp only [cost_seq, cost_lit, cost_ar, exec_lit, HS.setR_regs]
        rw [Function.update_apply, if_neg hio, hb1, Function.update_apply, if_pos rfl]
        have e1 : kappa B (RAM.bits 1) ≤ kappa B (RAM.bits N) := kappa_bits_le B (by omega)
        have e2 : kappa B (RAM.bits (k + 1)) ≤ kappa B (RAM.bits N) := kappa_bits_le B (by omega)
        omega)
  rw [hN'] at L
  obtain ⟨⟨L1, -⟩, L2⟩ := L
  refine ⟨L1, ?_⟩
  simp only [forLoop, cost_seq, cost_lit]
  rw [Finset.sum_add_distrib] at L2
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at L2
  have e0 : kappa B (RAM.bits 0) ≤ kappa B (RAM.bits N) := kappa_bits_le B (by omega)
  simp only [exec_lit] at *
  rw [hN'] at *
  nlinarith

end Loops

/-! ## Words stored in arrays -/

/-! ## Copying a block of cells -/

section Copy
variable (inp : ℕ → ℕ) (B : ℕ)

theorem copyW_spec_oai (S so D dO n j t u one : ℕ) (s : HS)
    (hreg : [S, so, D, dO, n, j, t, u, one].Nodup)
    (hSD : s.regs S ≠ s.regs D) (V M : ℕ)
    (hV : ∀ i < s.regs n, s.arr (s.regs S) (s.regs so + i) ≤ V)
    (hM : s.regs S + s.regs so + s.regs D + s.regs dO + s.regs n + V ≤ M) :
    (∀ i < s.regs n, ((copyW S so D dO n j t u one).exec inp s).arr (s.regs D) (s.regs dO + i) =
        s.arr (s.regs S) (s.regs so + i)) ∧
    (∀ y i, ¬ (y = s.regs D ∧ s.regs dO ≤ i ∧ i < s.regs dO + s.regs n) →
        ((copyW S so D dO n j t u one).exec inp s).arr y i = s.arr y i) ∧
    (∀ r, r ≠ j → r ≠ t → r ≠ u → r ≠ one →
        ((copyW S so D dO n j t u one).exec inp s).regs r = s.regs r) ∧
    ((copyW S so D dO n j t u one).exec inp s).cur = s.cur ∧
    ((copyW S so D dO n j t u one).exec inp s).out = s.out ∧
    (copyW S so D dO n j t u one).cost inp B s ≤ (7 * s.regs n + 3) * kappa B (RAM.bits M) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hreg
  obtain ⟨⟨hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8⟩, ⟨ho1, ho2, ho3, ho4, ho5, ho6, ho7⟩,
    ⟨hD1, hD2, hD3, hD4, hD5, hD6⟩, ⟨hd1, hd2, hd3, hd4, hd5⟩, ⟨hn1, hn2, hn3, hn4⟩,
    ⟨hj1, hj2, hj3⟩, ⟨ht1, ht2⟩, hu1, -⟩ := hreg
  set vS := s.regs S
  set vD := s.regs D
  set vso := s.regs so
  set vdo := s.regs dO
  have K := forLoop_spec inp B j n one
    (seqs [ar .add t so j, ald u S t, ar .add t dO j, ast D t u]) s hn1 hj3
    (fun k st => (∀ r, r ≠ j → r ≠ t → r ≠ u → r ≠ one → st.regs r = s.regs r) ∧
      (∀ i < k, st.arr vD (vdo + i) = s.arr vS (vso + i)) ∧
      (∀ y i, ¬ (y = vD ∧ vdo ≤ i ∧ i < vdo + k) → st.arr y i = s.arr y i) ∧
      st.cur = s.cur ∧ st.out = s.out)
    (fun _ => 4 * kappa B (RAM.bits M))
    ⟨fun r h1 _ _ _ => by simp [Function.update_apply, h1], fun i hi => absurd hi (Nat.not_lt_zero _),
      fun y i _ => rfl, rfl, rfl⟩
    (by
      intro k hk st ⟨hr, hc, hy, hcur, hout⟩ hj
      have eS : st.regs S = vS := hr S hS5 hS6 hS7 hS8
      have eD : st.regs D = vD := hr D hD3 hD4 hD5 hD6
      have eso : st.regs so = vso := hr so ho4 ho5 ho6 ho7
      have edo : st.regs dO = vdo := hr dO hd2 hd3 hd4 hd5
      have hsrc : st.arr vS (vso + k) = s.arr vS (vso + k) :=
        hy _ _ (fun h => hSD h.1)
      simp only [exec_seqs_cons, exec_seqs_nil, exec_ar, exec_ald, exec_ast, arith_add,
        HS.setR_regs, cost_seqs_cons, cost_seqs_nil, cost_ar, cost_ald, cost_ast,
        Function.update_apply, eS, eD, eso, edo, hj, HS.setR_arr, hsrc, HS.store_regs,
        hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, ho1, ho2, ho3, ho4, ho5, ho6, ho7,
        hD1, hD2, hD3, hD4, hD5, hD6, hd1, hd2, hd3, hd4, hd5, hn1, hn2, hn3, hn4,
        hj1, hj2, hj3, ht1, ht2, hu1, if_true, if_false, HS.setR_cur, HS.setR_out,
        HS.store_cur, HS.store_out, Ne.symm hS1, Ne.symm hS2, Ne.symm hS3, Ne.symm hS4, Ne.symm hS5, Ne.symm hS6, Ne.symm hS7, Ne.symm hS8, Ne.symm ho1, Ne.symm ho2, Ne.symm ho3, Ne.symm ho4, Ne.symm ho5, Ne.symm ho6, Ne.symm ho7, Ne.symm hD1, Ne.symm hD2, Ne.symm hD3, Ne.symm hD4, Ne.symm hD5, Ne.symm hD6, Ne.symm hd1, Ne.symm hd2, Ne.symm hd3, Ne.symm hd4, Ne.symm hd5, Ne.symm hn1, Ne.symm hn2, Ne.symm hn3, Ne.symm hn4, Ne.symm hj1, Ne.symm hj2, Ne.symm hj3, Ne.symm ht1, Ne.symm ht2, Ne.symm hu1]
      refine ⟨by simp, ⟨?_, ?_, ?_, by simp [hcur], by simp [hout]⟩, ?_⟩
      · intro r h1 h2 h3 h4
        simp [Function.update_apply, h1, h2, h3, h4, hr r h1 h2 h3 h4]
      · intro i hi
        simp only [HS.setR_arr, HS.store_arr]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
        · rw [if_neg (by omega)]; exact hc i hi
        · subst hi; simp
      · intro y i hyi
        simp only [HS.setR_arr, HS.store_arr]
        rw [if_neg (by omega)]
        exact hy y i (by omega)
      · have hvk := hV k hk
        have e1 := kappa_bits_le B (a := vso + k) (M := M) (by omega)
        have e2 := kappa_bits_le B (a := vS + (vso + k) + s.arr vS (vso + k)) (M := M) (by omega)
        have e3 := kappa_bits_le B (a := vdo + k) (M := M) (by omega)
        have e4 := kappa_bits_le B (a := vD + (vdo + k) + s.arr vS (vso + k)) (M := M) (by omega)
        omega)
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, hcost⟩ := K
  refine ⟨h2, h3, h1, h4, h5, ?_⟩
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hcost
  have := kappa_bits_le B (a := s.regs n) (M := M) (by omega)
  simp only [copyW]
  nlinarith

end Copy

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.copyW_spec_oai := @EditMulticoloring.Dev.Ram.copyW_spec_oai
