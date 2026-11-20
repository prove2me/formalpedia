-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.digitsW_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:34:43.838664+00:00
-- url     : https://prove2.me/submissions/ae7ac786-f192-432b-b3fb-aa99fd83d20d

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000
import Theorems.Thm_EditMulticoloring_Dev_Ram_exec_cur_of_reads
import Theorems.Thm_EditMulticoloring_Dev_Ram_exec_out_of_emits
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

/-! ### Horner evaluation -/

/-! ### Digits -/

theorem digitsW_spec_oai (r : ℕ) (s : HS) (M : ℕ)
    (hM : s.regs r + s.regs (r + 1) + s.regs (r + 2) + s.regs (r + 3) + s.regs (r + 4) ≤ M) :
    (∀ i < s.regs (r + 2), ((digitsW r).exec inp s).arr (s.regs (r + 3)) (s.regs (r + 4) + i) =
      (s.regs r / s.regs (r + 1) ^ i) % s.regs (r + 1)) ∧
    (∀ y i, ¬ (y = s.regs (r + 3) ∧ s.regs (r + 4) ≤ i ∧ i < s.regs (r + 4) + s.regs (r + 2)) →
      ((digitsW r).exec inp s).arr y i = s.arr y i) ∧
    (∀ r', (r' < r + 5 ∨ r + 10 ≤ r') → ((digitsW r).exec inp s).regs r' = s.regs r') ∧
    ((digitsW r).exec inp s).cur = s.cur ∧
    ((digitsW r).exec inp s).out = s.out ∧
    (digitsW r).cost inp B s ≤ (7 * s.regs (r + 2) + 4) * kappa B (RAM.bits M) := by
  set v := s.regs r
  set q := s.regs (r + 1)
  set vD := s.regs (r + 3)
  set voff := s.regs (r + 4)
  set s1 := s.setR (r + 5) v with hs1
  have hn1 : s1.regs (r + 2) = s.regs (r + 2) := by simp [hs1]
  have K := forLoop_spec inp B (r + 6) (r + 2) (r + 9) (seqs [ar .add (r + 7) (r + 4) (r + 6),
    ar .mod (r + 8) (r + 5) (r + 1), ast (r + 3) (r + 7) (r + 8), ar .div (r + 5) (r + 5) (r + 1)])
    s1 (by omega) (by omega)
    (fun k st => st.regs (r + 5) = v / q ^ k ∧
      (∀ i < k, st.arr vD (voff + i) = (v / q ^ i) % q) ∧
      (∀ y i, ¬ (y = vD ∧ voff ≤ i ∧ i < voff + k) → st.arr y i = s.arr y i) ∧
      (∀ r', (r' < r + 5 ∨ r + 10 ≤ r') → st.regs r' = s.regs r'))
    (fun _ => 4 * kappa B (RAM.bits M))
    ⟨by simp [hs1], fun i hi => absurd hi (Nat.not_lt_zero _), fun y i _ => by simp [hs1],
      fun r' h => by simp (disch := omega) [hs1, upd_ne]⟩
    (by
      intro k hk st ⟨hw, hc, hy, hr⟩ hj
      rw [hn1] at hk
      have eq : st.regs (r + 1) = q := hr _ (by omega)
      have eD : st.regs (r + 3) = vD := hr _ (by omega)
      have eoff : st.regs (r + 4) = voff := hr _ (by omega)
      have hle : v / q ^ k ≤ v := Nat.div_le_self _ _
      have hmod : v / q ^ k % q ≤ v / q ^ k := Nat.mod_le _ _
      simp (disch := omega) only [exec_seqs_cons, exec_seqs_nil, exec_ar, exec_ast,
        arith_add, arith_mod, arith_div, HS.setR_regs, HS.store_regs,
        upd_ne, upd_eq, eD, eoff, eq, hj, hw, cost_seqs_cons, cost_seqs_nil, cost_ar,
        cost_ast]
      refine ⟨by simp (disch := omega) [upd_ne, hj], ⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · try simp (disch := omega) only [upd_ne, upd_eq, HS.setR_regs, HS.store_regs]
        rw [Nat.div_div_eq_div_mul, pow_succ]
      · intro i hi
        simp only [HS.setR_arr, HS.store_arr]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · rw [if_neg (by omega)]; exact hc i hi
        · simp
      · intro y i hyi
        simp only [HS.setR_arr, HS.store_arr]
        rw [if_neg (by omega)]; exact hy y i (by omega)
      · intro r' h
        simp (disch := omega) only [upd_ne, HS.setR_regs, HS.store_regs]; exact hr r' h
      · have e1 := kappa_bits_le B (a := voff + k) (M := M) (by omega)
        have e2 := kappa_bits_le B (a := v / q ^ k + q) (M := M) (by omega)
        have e3 := kappa_bits_le B (a := vD + (voff + k) + v / q ^ k % q) (M := M) (by omega)
        omega)
  rw [hn1] at K
  obtain ⟨⟨-, k2, k3, k4⟩, k5⟩ := K
  have hcur : ((digitsW r).exec inp s).cur = s.cur := exec_cur_of_reads inp _ rfl s
  have hout : ((digitsW r).exec inp s).out = s.out := exec_out_of_emits inp _ rfl s
  refine ⟨k2, k3, k4, hcur, hout, ?_⟩
  have hc : (digitsW r).cost inp B s = kappa B (RAM.bits v) +
      (forLoop (r + 6) (r + 2) (r + 9) (seqs [ar .add (r + 7) (r + 4) (r + 6),
    ar .mod (r + 8) (r + 5) (r + 1), ast (r + 3) (r + 7) (r + 8), ar .div (r + 5) (r + 5) (r + 1)])).cost
      inp B s1 := rfl
  rw [hc]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at k5
  have := kappa_bits_le B (a := s.regs (r + 2)) (M := M) (by omega)
  have := kappa_bits_le B (a := v) (M := M) (by omega)
  nlinarith

end Utils

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.digitsW_spec_oai := @EditMulticoloring.Dev.Ram.digitsW_spec_oai
