-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.EncS.reprW_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:34:32.675937+00:00
-- url     : https://prove2.me/submissions/e45614c0-bdad-4843-9f02-75d541416ecb

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Construction
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000
import Theorems.Thm_EditMulticoloring_Dev_Ram_kappa_bits_le
import Theorems.Thm_EditMulticoloring_Dev_Ram_upd_eq
import Theorems.Thm_EditMulticoloring_Dev_Ram_upd_ne

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

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamEncodeS1
attribute [-simp] _root_.EditMulticoloring.Dev.Ram.arith_xor
/-! Verbatim copy of `RamShort.lean` (q379, Part S) in namespace `EditMulticoloring.Dev.Ram.EncS`:
the original clashes with `RamColor` on the names `value_lt` and `visBound`, so the two chains
cannot be imported together; the encoder uses this copy. -/

/-!
# Short table, part 1: words, values, representations, greedy (q379, Part S)

* `value_cons`, `value_lt`, `value_inj` — `value` is a bijection from words of length `l`
  onto `[0, q^l)`;
* `repr_length`, `repr_getElem`, `value_repr`, `repr_value` — `Code.repr q l` is its inverse;
* `words_eq` — `words q l = (List.range (q^l)).map (Code.repr q l)`;
* `greedy` facts: sublist of the input, no duplicates, lengths;
* the RAM routine `reprW` writing the digits of a number (`repr`) into an array.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram.EncS

open EditMulticoloring.Code

/-! ## `value` -/

/-! ## `repr` -/

/-! ## `words` -/

/-! ## `greedy` -/

/-! ## Writing the digits of a number -/

section Repr
variable (inp : ℕ → ℕ) (B : ℕ)

theorem reprW_spec_oai (r : ℕ) (s : HS) (M : ℕ) (hQ : 0 < s.regs (r + 4))
    (hP : s.regs (r + 2) = s.regs (r + 4) ^ s.regs (r + 3))
    (hM : s.regs r + s.regs (r + 1) + s.regs (r + 3) + s.regs (r + 4) +
      s.regs (r + 4) ^ s.regs (r + 3) ≤ M) :
    (∀ i < s.regs (r + 3), ((reprW r).exec inp s).arr (s.regs r) i =
      (s.regs (r + 1) / s.regs (r + 4) ^ (s.regs (r + 3) - 1 - i)) % s.regs (r + 4)) ∧
    (∀ y i, ¬ (y = s.regs r ∧ i < s.regs (r + 3)) → ((reprW r).exec inp s).arr y i = s.arr y i) ∧
    (∀ r', r' ≠ r + 2 → r' ≠ r + 5 → r' ≠ r + 6 → r' ≠ r + 7 →
      ((reprW r).exec inp s).regs r' = s.regs r') ∧
    ((reprW r).exec inp s).cur = s.cur ∧
    ((reprW r).exec inp s).out = s.out ∧
    (reprW r).cost inp B s ≤ (7 * s.regs (r + 3) + 3) * kappa B (RAM.bits M) := by
  set vX := s.regs r
  set V := s.regs (r + 1)
  set n := s.regs (r + 3)
  set Q := s.regs (r + 4)
  have K := forLoop_spec inp B (r + 5) (r + 3) (r + 7) (seqs [ar .div (r + 2) (r + 2) (r + 4),
    ar .div (r + 6) (r + 1) (r + 2), ar .mod (r + 6) (r + 6) (r + 4), ast r (r + 5) (r + 6)]) s
    (by omega) (by omega)
    (fun k st => st.regs (r + 2) = Q ^ (n - k) ∧
      (∀ r', r' ≠ r + 2 → r' ≠ r + 5 → r' ≠ r + 6 → r' ≠ r + 7 → st.regs r' = s.regs r') ∧
      (∀ i < k, st.arr vX i = (V / Q ^ (n - 1 - i)) % Q) ∧
      (∀ y i, ¬ (y = vX ∧ i < k) → st.arr y i = s.arr y i) ∧
      st.cur = s.cur ∧ st.out = s.out)
    (fun _ => 4 * kappa B (RAM.bits M))
    ⟨by simp (disch := omega) [upd_ne, hP], fun r' h1 _ _ _ => by simp (disch := omega) [upd_ne, h1],
      fun i hi => absurd hi (Nat.not_lt_zero _), fun _ _ _ => rfl, rfl, rfl⟩
    (by
      intro k hk st ⟨hp, hr, hc, hy, hcur, hout⟩ hj
      have eX : st.regs r = vX := hr r (by omega) (by omega) (by omega) (by omega)
      have eV : st.regs (r + 1) = V := hr _ (by omega) (by omega) (by omega) (by omega)
      have eQ : st.regs (r + 4) = Q := hr _ (by omega) (by omega) (by omega) (by omega)
      have hpow : Q ^ (n - k) / Q = Q ^ (n - 1 - k) := by
        rw [show n - k = (n - 1 - k) + 1 by omega, pow_succ, Nat.mul_div_cancel _ hQ]
      have hle : Q ^ (n - k) ≤ Q ^ n := Nat.pow_le_pow_right hQ (by omega)
      have hle' : Q ^ (n - 1 - k) ≤ Q ^ n := Nat.pow_le_pow_right hQ (by omega)
      have hdl : V / Q ^ (n - 1 - k) % Q < Q := Nat.mod_lt _ hQ
      simp (disch := omega) only [exec_seqs_cons, exec_seqs_nil, exec_ar, exec_ast,
        arith_div, arith_mod, HS.setR_regs, HS.setR_arr, HS.store_regs, upd_ne, upd_eq, eX, eV, eQ,
        hj, hp, hpow, cost_seqs_cons, cost_seqs_nil, cost_ar, cost_ast]
      refine ⟨by simp (disch := omega) [upd_ne, hj], ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [show n - (k + 1) = n - 1 - k by omega]
      · intro r' h1 h2 h3 h4
        simp (disch := omega) only [upd_ne, HS.setR_regs, HS.store_regs]; exact hr r' h1 h2 h3 h4
      · intro i hi
        simp only [HS.setR_arr, HS.store_arr]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
        · rw [if_neg (by omega)]; exact hc i hi
        · subst hi; simp
      · intro y i hyi
        simp only [HS.setR_arr, HS.store_arr]
        rw [if_neg (by omega)]
        exact hy y i (by omega)
      · simp [hcur]
      · simp [hout]
      · have hdiv : V / Q ^ (n - 1 - k) ≤ V := Nat.div_le_self _ _
        have e1 := kappa_bits_le B (a := Q ^ (n - k) + Q) (M := M) (by omega)
        have e2 := kappa_bits_le B (a := V + Q ^ (n - 1 - k)) (M := M) (by omega)
        have e3 := kappa_bits_le B (a := V / Q ^ (n - 1 - k) + Q) (M := M) (by omega)
        have e4 := kappa_bits_le B (a := vX + k + V / Q ^ (n - 1 - k) % Q) (M := M) (by omega)
        omega)
  obtain ⟨⟨-, h1, h2, h3, h4, h5⟩, hcost⟩ := K
  refine ⟨h2, h3, h1, h4, h5, ?_⟩
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hcost
  have := kappa_bits_le B (a := n) (M := M) (by omega)
  simp only [reprW]
  nlinarith

end Repr

end EditMulticoloring.Dev.Ram.EncS
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.EncS.reprW_spec_oai := @EditMulticoloring.Dev.Ram.EncS.reprW_spec_oai
