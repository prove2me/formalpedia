-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.readW_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:37:31.311089+00:00
-- url     : https://prove2.me/submissions/2aab2bc3-f265-4dff-9ca0-cfe26fc753c7

import Mathlib
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

theorem one_le_bits (a : ℕ) : 1 ≤ RAM.bits a := by unfold RAM.bits; omega

theorem kappa_mono {B B' W W' : ℕ} (hB : B ≤ B') (hW : W ≤ W') : kappa B W ≤ kappa B' W' := by
  unfold kappa
  have : (W + 2) ^ 2 ≤ (W' + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  omega

theorem kappa_mono_right (B : ℕ) {W W' : ℕ} (hW : W ≤ W') : kappa B W ≤ kappa B W' :=
  kappa_mono le_rfl hW

theorem kappa_zero_le (B M : ℕ) : kappa B 0 ≤ kappa B (RAM.bits M) :=
  kappa_mono_right B (Nat.zero_le _)

theorem kappa_one_le (B M : ℕ) : kappa B 1 ≤ kappa B (RAM.bits M) :=
  kappa_mono_right B (one_le_bits M)

theorem kappa_bits_one_le (B M : ℕ) : kappa B (RAM.bits 1) ≤ kappa B (RAM.bits M) := by
  rw [bits_one]; exact kappa_one_le B M

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
-- module Solutions.EditMulticoloring.RamLib2
attribute [-simp] _root_.EditMulticoloring.Dev.Ram.arith_xor
/-!
# Word utilities on `Cmd` (q379, Part L)

Each utility is a counted loop on registers given as parameters; every spec gives the effect,
the frame (registers outside the written list, memory, cursor, output) and a cost bound of the
form `(a * N + b) * kappa B (RAM.bits M)` under a data bound `… ≤ M`.

* `eqW`     — compare two stored blocks (flag register: 1 iff equal);
* `emitW`   — emit a stored block;
* `readW`   — read `N` input symbols, storing `v - 1`;
* `readRun` — the same, also computing the length of the leading non-EOF run (`runLen`);
* `valueW`  — Horner evaluation `V := q * V + a` (`= EditMulticoloring.Code.value`);
* `digitsW` — `D[off + i] := (V / Q ^ i) % Q` for `i < K`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

section Utils
variable (inp : ℕ → ℕ) (B : ℕ)

/-! ### Equality test -/

/-! ### Emitting a stored block -/

/-! ### Reading input -/

theorem runLen_succ_zero (g : ℕ → ℕ) (c k : ℕ) (h : g (c + k) = 0) :
    runLen g c (k + 1) = runLen g c k := by
  simp [runLen, h]

theorem runLen_succ_ne (g : ℕ → ℕ) (c k : ℕ) (h : g (c + k) ≠ 0) :
    runLen g c (k + 1) = if runLen g c k = k then k + 1 else runLen g c k := by
  simp [runLen, h]

theorem runLen_le (g : ℕ → ℕ) (c k : ℕ) : runLen g c k ≤ k := by
  induction k with
  | zero => simp [runLen]
  | succ k ih => simp only [runLen]; split_ifs <;> omega

theorem readW_spec_oai (r : ℕ) (s : HS) (V M : ℕ)
    (hV : ∀ i < s.regs (r + 2), inp (s.cur + i) ≤ V)
    (hM : s.regs r + s.regs (r + 1) + s.regs (r + 2) + s.cur + V + 1 ≤ M) :
    (∀ i < s.regs (r + 2), ((readW r).exec inp s).arr (s.regs r) (s.regs (r + 1) + i) =
      inp (s.cur + i) - 1) ∧
    (∀ y i, ¬ (y = s.regs r ∧ s.regs (r + 1) ≤ i ∧ i < s.regs (r + 1) + s.regs (r + 2)) →
      ((readW r).exec inp s).arr y i = s.arr y i) ∧
    ((readW r).exec inp s).regs (r + 3) = runLen inp s.cur (s.regs (r + 2)) ∧
    (∀ r', (r' < r + 3 ∨ r + 9 ≤ r') → ((readW r).exec inp s).regs r' = s.regs r') ∧
    ((readW r).exec inp s).cur = s.cur + s.regs (r + 2) ∧
    ((readW r).exec inp s).out = s.out ∧
    (readW r).cost inp B s ≤ (11 * s.regs (r + 2) + 6) * kappa B (RAM.bits M) := by
  set vX := s.regs r
  set voff := s.regs (r + 1)
  set s1 := (s.setR (r + 3) 0).setR (r + 4) 1 with hs1
  have hn1 : s1.regs (r + 2) = s.regs (r + 2) := by simp [hs1]
  have K := forLoop_spec inp B (r + 5) (r + 2) (r + 8)
    (seqs [rd (r + 7), .ifz (r + 7) (lit (r + 4) 0) .skip, ar .add (r + 3) (r + 3) (r + 4),
      lit (r + 8) 1, ar .sub (r + 7) (r + 7) (r + 8), ar .add (r + 6) (r + 1) (r + 5),
      ast r (r + 6) (r + 7)]) s1
    (by omega) (by omega)
    (fun k st => (∀ i < k, st.arr vX (voff + i) = inp (s.cur + i) - 1) ∧
      (∀ y i, ¬ (y = vX ∧ voff ≤ i ∧ i < voff + k) → st.arr y i = s.arr y i) ∧
      st.regs (r + 3) = runLen inp s.cur k ∧
      st.regs (r + 4) = (if runLen inp s.cur k = k then 1 else 0) ∧
      (∀ r', (r' < r + 3 ∨ r + 9 ≤ r') → st.regs r' = s.regs r') ∧
      st.cur = s.cur + k ∧ st.out = s.out)
    (fun _ => 8 * kappa B (RAM.bits M))
    ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun y i _ => by simp [hs1],
      by simp (disch := omega) [hs1, upd_ne, runLen], by simp (disch := omega) [hs1, upd_ne, runLen],
      fun r' h => by simp (disch := omega) [hs1, upd_ne], by simp [hs1], by simp [hs1]⟩
    (by
      intro k hk st ⟨ha, hy, hlen, hf, hr, hc, ho⟩ hj
      rw [hn1] at hk
      have eX : st.regs r = vX := hr r (by omega)
      have eoff : st.regs (r + 1) = voff := hr _ (by omega)
      have hVk := hV k hk
      have hrun := runLen_le inp s.cur k
      set g := inp (s.cur + k) with hg
      have hcg : inp st.cur = g := by rw [hc]
      simp (disch := omega) only [exec_seqs_cons, exec_seqs_nil, exec_ar, exec_ast, exec_rd,
        exec_lit, exec_ifz, exec_skip, arith_add, arith_sub, HS.setR_regs, HS.setR_arr,
        HS.setR_cur, HS.setR_out, HS.store_regs, HS.store_cur, HS.store_out,
        upd_ne, upd_eq, eX, eoff, hj, hcg, cost_seqs_cons, cost_seqs_nil, cost_ar,
        cost_ast, cost_rd, cost_lit, cost_ifz, cost_skip, Function.update_self]
      have e1 := kappa_bits_le B (a := st.cur + g) (M := M) (by omega)
      have e2 := kappa_bits_le B (a := g) (M := M) (by omega)
      have e3 := kappa_bits_le B (a := 0) (M := M) (by omega)
      have e4 := kappa_bits_le B (a := runLen inp s.cur k + 1) (M := M) (by omega)
      have e4' := kappa_bits_le B (a := runLen inp s.cur k + 0) (M := M) (by omega)
      have e5 := kappa_bits_one_le B M
      have e6 := kappa_bits_le B (a := g + 1) (M := M) (by omega)
      have e7 := kappa_bits_le B (a := voff + k) (M := M) (by omega)
      have e8 := kappa_bits_le B (a := vX + (voff + k) + (g - 1)) (M := M) (by omega)
      have hrk' := runLen_le inp s.cur k
      by_cases hg0 : g = 0
      · have hg0' : inp (s.cur + k) = 0 := by rw [← hg]; exact hg0
        rw [runLen_succ_zero inp s.cur k hg0']
        simp only [hg0, if_true]
        refine ⟨by simp (disch := omega) [upd_ne, hj], ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · intro i hi
          simp (disch := omega) only [HS.setR_arr, HS.store_arr, eX, eoff, hj, upd_ne, upd_eq,
            HS.setR_regs]
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
          · rw [if_neg (by omega)]; exact ha i hi
          · simp [hg0, hg0']
        · intro y i hyi
          simp (disch := omega) only [HS.setR_arr, HS.store_arr, eX, eoff, hj, upd_ne, upd_eq,
            HS.setR_regs]
          rw [if_neg (by omega)]; exact hy y i (by omega)
        · simp (disch := omega) only [upd_ne, upd_eq, HS.setR_regs, HS.store_regs]
          simp [hlen]
        · simp (disch := omega) only [upd_ne, upd_eq, HS.setR_regs, HS.store_regs]
          rw [if_neg (by omega)]
        · intro r' h
          simp (disch := omega) only [upd_ne, HS.setR_regs, HS.store_regs]; exact hr r' h
        · simp [hc]; omega
        · simpa using ho
        · simp (disch := omega) only [upd_ne, upd_eq, HS.store_regs, HS.setR_regs, HS.setR_cur,
            HS.store_cur, eX, eoff, hj, hlen, hf, hc, hg0, Nat.add_zero, Nat.zero_add]
          have f1 := kappa_bits_le B (a := s.cur + k) (M := M) (by omega)
          have f2 := kappa_bits_le B (a := runLen inp s.cur k) (M := M) (by omega)
          have f3 := kappa_bits_le B (a := vX + (voff + k) + (0 - 1)) (M := M) (by omega)
          omega
      · have hg0' : inp (s.cur + k) ≠ 0 := by rw [← hg]; exact hg0
        rw [runLen_succ_ne inp s.cur k hg0']
        simp only [hg0, if_false]
        refine ⟨by simp (disch := omega) [upd_ne, hj], ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · intro i hi
          simp (disch := omega) only [HS.setR_arr, HS.store_arr, eX, eoff, hj, upd_ne, upd_eq,
            HS.setR_regs]
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
          · rw [if_neg (by omega)]; exact ha i hi
          · simp [hg]
        · intro y i hyi
          simp (disch := omega) only [HS.setR_arr, HS.store_arr, eX, eoff, hj, upd_ne, upd_eq,
            HS.setR_regs]
          rw [if_neg (by omega)]; exact hy y i (by omega)
        · simp (disch := omega) only [upd_ne, upd_eq, HS.setR_regs, HS.store_regs, hlen, hf]
          by_cases hrk : runLen inp s.cur k = k
          · rw [if_pos hrk, if_pos hrk, hrk]
          · rw [if_neg hrk, if_neg hrk]; simp
        · simp (disch := omega) only [upd_ne, upd_eq, HS.setR_regs, HS.store_regs, hf]
          by_cases hrk : runLen inp s.cur k = k
          · rw [if_pos hrk, if_pos hrk, if_pos rfl]
          · rw [if_neg hrk, if_neg hrk, if_neg (by omega)]
        · intro r' h
          simp (disch := omega) only [upd_ne, HS.setR_regs, HS.store_regs]; exact hr r' h
        · simp [hc]; omega
        · simpa using ho
        · simp (disch := omega) only [upd_ne, upd_eq, HS.store_regs, HS.setR_regs, HS.setR_cur,
            HS.store_cur, eX, eoff, hj, hlen, hf, hc, Nat.add_zero, Nat.zero_add]
          have f1 := kappa_bits_le B (a := s.cur + k + g) (M := M) (by omega)
          split_ifs <;> omega)
  rw [hn1] at K
  obtain ⟨⟨k1, k2, k3, -, k5, k6, k7⟩, k8⟩ := K
  have hex : (readW r).exec inp s = (forLoop (r + 5) (r + 2) (r + 8)
    (seqs [rd (r + 7), .ifz (r + 7) (lit (r + 4) 0) .skip, ar .add (r + 3) (r + 3) (r + 4),
      lit (r + 8) 1, ar .sub (r + 7) (r + 7) (r + 8), ar .add (r + 6) (r + 1) (r + 5),
      ast r (r + 6) (r + 7)])).exec inp s1 := rfl
  rw [hex]
  refine ⟨k1, k2, k3, fun r' h => (k5 r' h), k6, k7, ?_⟩
  have hc : (readW r).cost inp B s = kappa B (RAM.bits 0) + (kappa B (RAM.bits 1) +
      ((forLoop (r + 5) (r + 2) (r + 8)
    (seqs [rd (r + 7), .ifz (r + 7) (lit (r + 4) 0) .skip, ar .add (r + 3) (r + 3) (r + 4),
      lit (r + 8) 1, ar .sub (r + 7) (r + 7) (r + 8), ar .add (r + 6) (r + 1) (r + 5),
      ast r (r + 6) (r + 7)])).cost inp B s1 + 0)) := rfl
  rw [hc]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at k8
  have := kappa_bits_le B (a := s.regs (r + 2)) (M := M) (by omega)
  have := kappa_bits_one_le B M
  have := kappa_bits_le B (a := 0) (M := M) (by omega)
  nlinarith

/-! ### Horner evaluation -/

/-! ### Digits -/

end Utils

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.readW_spec_oai := @EditMulticoloring.Dev.Ram.readW_spec_oai
