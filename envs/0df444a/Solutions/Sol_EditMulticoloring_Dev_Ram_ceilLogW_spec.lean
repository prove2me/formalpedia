-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.ceilLogW_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:34:39.659113+00:00
-- url     : https://prove2.me/submissions/efe1de73-aae0-4cbf-9fc5-5ec350540e3d

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Construction
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000
import Theorems.Thm_EditMulticoloring_Dev_Ram_exec_cur_of_reads
import Theorems.Thm_EditMulticoloring_Dev_Ram_exec_mem_of_stores
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

section Frames
variable (inp : ℕ → ℕ)

theorem iterate_induct {f : HS → HS} (P : HS → Prop) (h : ∀ s, P s → P (f s)) :
    ∀ (n : ℕ) (s : HS), P s → P (f^[n] s)
  | 0, _, hs => hs
  | n + 1, s, hs => by rw [Function.iterate_succ_apply]; exact iterate_induct P h n _ (h _ hs)

theorem exec_regs_of_not_mem (c : Cmd) {r : ℕ} (h : r ∉ c.wregs) (s : HS) :
    (c.exec inp s).regs r = s.regs r := by
  induction c generalizing s with
  | prim p =>
    cases p <;> simp_all [Cmd.wregs, Cmd.exec, Prim.exec]
  | seq c₁ c₂ ih₁ ih₂ =>
    simp only [Cmd.wregs, List.mem_append, not_or] at h
    simp [ih₁ h.1, ih₂ h.2]
  | ifz a c₁ c₂ ih₁ ih₂ =>
    simp only [Cmd.wregs, List.mem_append, not_or] at h
    simp only [exec_ifz]; split_ifs
    · exact ih₁ h.1 s
    · exact ih₂ h.2 s
  | loop a c ih =>
    simp only [Cmd.wregs] at h
    rw [exec_loop]
    exact iterate_induct (fun t => t.regs r = s.regs r) (fun t ht => (ih h t).trans ht) _ _ rfl
  | skip => rfl

end Frames

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

end Loops

/-! ## Words stored in arrays -/

/-! ## Copying a block of cells -/

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamParams
attribute [-simp] _root_.EditMulticoloring.Dev.Ram.arith_xor
/-!
# Part P (q379): logarithms and powers

Register convention: inputs in arbitrary registers below `S`; outputs at `S`, `S + 1`, …;
scratch above the outputs.  Each program's frame lemma lists the registers it may write.

* `floorLogW b N T S`: `S := Nat.log (regs b) (regs N)`, `S+1 := regs b ^ (regs S)`
  (needs `Nat.log … ≤ regs T`, loop count `regs T`); writes `S .. S+3`.
* `ceilLogW b N T S`: `S := ceilLog (regs b) (regs N)`, `S+1 := regs b ^ (regs S)`; `S .. S+3`.
* `powW a e S`: `S := regs a ^ regs e`; writes only `S`.
* `radW q t lR S`: `S := radiusBound q (2 t) (regs lR)`; writes `S .. S+2`.
* `rhoW q t nR hR qhR S`: `S := shortLength q t (regs hR)`; writes `S .. S+8`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

section Logs
variable (inp : ℕ → ℕ) (B : ℕ)

theorem floorLogBody_wregs (b N S : ℕ) :
    (floorLogBody b N S).wregs = [S + 2, S + 3, S + 1, S + 3, S] := rfl

theorem floorLogW_spec (b N T S : ℕ) (s : HS) (M : ℕ) (hb : b < S) (hN : N < S) (hT : T < S)
    (h2 : 2 ≤ s.regs b) (hlog : Nat.log (s.regs b) (s.regs N) ≤ s.regs T)
    (hM : (s.regs N + 2) * (s.regs b + 1) + s.regs T ≤ M) :
    ((floorLogW b N T S).exec inp s).regs S = Nat.log (s.regs b) (s.regs N) ∧
    ((floorLogW b N T S).exec inp s).regs (S + 1) = s.regs b ^ Nat.log (s.regs b) (s.regs N) ∧
    (∀ r', (r' < S ∨ S + 4 ≤ r') → ((floorLogW b N T S).exec inp s).regs r' = s.regs r') ∧
    ((floorLogW b N T S).exec inp s).mem = s.mem ∧
    ((floorLogW b N T S).exec inp s).cur = s.cur ∧
    ((floorLogW b N T S).exec inp s).out = s.out ∧
    (floorLogW b N T S).cost inp B s ≤ (7 * s.regs T + 4) * kappa B (RAM.bits M) := by
  set bq := s.regs b with hbq
  set n := s.regs N with hn
  set L := Nat.log bq n with hL
  set s1 := (s.setR S 0).setR (S + 1) 1 with hs1
  have hT1 : s1.regs T = s.regs T := by simp (disch := omega) [hs1, upd_ne]
  have K := loop_spec inp B T (floorLogBody b N S) s1
    (fun k st => st.regs S = min k L ∧ st.regs (S + 1) = bq ^ min k L ∧
      ∀ r', (r' < S ∨ S + 4 ≤ r') → st.regs r' = s.regs r')
    (fun _ => 6 * kappa B (RAM.bits M))
    ⟨by simp (disch := omega) [hs1, upd_ne], by simp (disch := omega) [hs1, upd_ne],
      fun r' h => by simp (disch := omega) [hs1, upd_ne]⟩
    (by
      intro k hk st ⟨hc, hP, hr⟩
      rw [hT1] at hk
      have eb : st.regs b = bq := hr b (Or.inl hb)
      have eN : st.regs N = n := hr N (Or.inl hN)
      have hPle : bq ^ min k L ≤ n + 1 := by
        rcases Nat.eq_zero_or_pos n with h0 | h0
        · have : L = 0 := by rw [hL, h0]; simp
          rw [this]; simp
        · have := Nat.pow_log_le_self bq h0.ne'
          rw [← hL] at this
          have := Nat.pow_le_pow_right (show 1 ≤ bq by omega) (min_le_right k L)
          omega
      have hprod : bq ^ min k L * bq ≤ (n + 1) * bq := Nat.mul_le_mul_right _ hPle
      have hexp : (n + 2) * (bq + 1) = (n + 1) * bq + bq + n + 2 := by ring
      have hn1 : n + 1 ≤ (n + 1) * bq := Nat.le_mul_of_pos_right _ (by omega)
      have hframe : ∀ r', (r' < S ∨ S + 4 ≤ r') → ((floorLogBody b N S).exec inp st).regs r' = s.regs r' := by
        intro r' h
        rw [exec_regs_of_not_mem inp _ (by rw [floorLogBody_wregs]; simp only [List.mem_cons,
          List.not_mem_nil, or_false, not_or]; omega)]
        exact hr r' h
      by_cases hkL : k < L
      · have hm : min k L = k := min_eq_left hkL.le
        have hm1 : min (k + 1) L = k + 1 := min_eq_left hkL
        rw [hm] at hc hP hprod hPle
        have hn0 : n ≠ 0 := by intro h0; rw [hL, h0] at hkL; simp at hkL
        have hle : bq ^ k * bq ≤ n := by
          rw [← pow_succ]
          exact (Nat.pow_le_pow_right (by omega) hkL).trans (Nat.pow_log_le_self bq hn0)
        have hlt : ¬ n < bq ^ k * bq := by omega
        refine ⟨⟨?_, ?_, hframe⟩, ?_⟩
        · simp (disch := omega) [floorLogBody, upd_ne, upd_eq, eb, eN, hc, hP, hlt, hm1]
        · simp (disch := omega) [floorLogBody, upd_ne, upd_eq, eb, eN, hc, hP, hlt, hm1, pow_succ]
        · simp (disch := omega) only [floorLogBody, cost_seqs_cons, cost_seqs_nil, cost_ar, cost_ifz,
            cost_cp, cost_lit, exec_seqs_cons, exec_ar, exec_cp, exec_lit, HS.setR_regs, upd_ne,
            upd_eq, eb, eN, hc, hP, arith_mul, arith_lt, hlt, if_false, if_true, arith_add]
          have e1 := kappa_bits_le B (a := bq ^ k + bq) (M := M) (by omega)
          have e2 := kappa_bits_le B (a := n + bq ^ k * bq) (M := M) (by omega)
          have e3 := kappa_bits_le B (a := (0 : ℕ)) (M := M) (by omega)
          have e4 := kappa_bits_le B (a := bq ^ k * bq) (M := M) (by omega)
          have e5 := kappa_bits_le B (a := (1 : ℕ)) (M := M) (by omega)
          have e6 := kappa_bits_le B (a := k + 1) (M := M) (by omega)
          omega
      · have hm : min k L = L := min_eq_right (by omega)
        have hm1 : min (k + 1) L = L := min_eq_right (by omega)
        rw [hm] at hc hP hprod hPle
        have hgt : n < bq ^ L * bq := by
          rw [← pow_succ]; exact Nat.lt_pow_succ_log_self (by omega) n
        refine ⟨⟨?_, ?_, hframe⟩, ?_⟩
        · simp (disch := omega) [floorLogBody, upd_ne, upd_eq, eb, eN, hc, hP, hgt, hm1]
        · simp (disch := omega) [floorLogBody, upd_ne, upd_eq, eb, eN, hc, hP, hgt, hm1]
        · simp (disch := omega) only [floorLogBody, cost_seqs_cons, cost_seqs_nil, cost_ar, cost_ifz,
            cost_cp, cost_lit, cost_skip, exec_seqs_cons, exec_ar, exec_cp, exec_lit, HS.setR_regs,
            upd_ne, upd_eq, eb, eN, hc, hP, arith_mul, arith_lt, hgt, if_false, if_true, arith_add,
            one_ne_zero]
          have e1 := kappa_bits_le B (a := bq ^ L + bq) (M := M) (by omega)
          have e2 := kappa_bits_le B (a := n + bq ^ L * bq) (M := M) (by omega)
          have e3 := kappa_bits_le B (a := (1 : ℕ)) (M := M) (by omega)
          omega)
  obtain ⟨⟨k1, k2, k3⟩, k4⟩ := K
  simp only [hT1] at k1 k2 k4
  have hmin : min (s.regs T) L = L := min_eq_right hlog
  rw [hmin] at k1 k2
  have hex : (floorLogW b N T S).exec inp s = (Cmd.loop T (floorLogBody b N S)).exec inp s1 := rfl
  have hco : (floorLogW b N T S).cost inp B s = kappa B (RAM.bits 0) + (kappa B (RAM.bits 1) +
      ((Cmd.loop T (floorLogBody b N S)).cost inp B s1 + 0)) := rfl
  refine ⟨by rw [hex]; exact k1, by rw [hex]; exact k2, by rw [hex]; exact k3,
    exec_mem_of_stores inp _ rfl s, exec_cur_of_reads inp _ rfl s, exec_out_of_emits inp _ rfl s, ?_⟩
  rw [hco]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at k4
  have := kappa_bits_le B (a := s.regs T) (M := M) (by omega)
  have := kappa_bits_le B (a := 0) (M := M) (by omega)
  have : 1 ≤ (n + 2) * (bq + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have := kappa_bits_le B (a := 1) (M := M) (by omega)
  nlinarith

theorem ceilLogW_frame (b N T S : ℕ) (s : HS) (r' : ℕ) (h : r' < S ∨ S + 4 ≤ r') :
    ((ceilLogW b N T S).exec inp s).regs r' = s.regs r' := by
  apply exec_regs_of_not_mem
  simp only [ceilLogW, floorLogW, floorLogBody, seqs, Cmd.wregs, lit, ar, cp, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, and_true, true_and]
  omega

theorem ceilLogW_spec_oai (b N T S : ℕ) (s : HS) (M : ℕ) (hb : b < S) (hN : N < S) (hT : T < S)
    (h2 : 2 ≤ s.regs b) (hlog : Nat.log (s.regs b) (s.regs N) ≤ s.regs T)
    (hM : (s.regs N + 2) * (s.regs b + 1) + s.regs T ≤ M) :
    ((ceilLogW b N T S).exec inp s).regs S = ceilLog (s.regs b) (s.regs N) ∧
    ((ceilLogW b N T S).exec inp s).regs (S + 1) = s.regs b ^ ceilLog (s.regs b) (s.regs N) ∧
    (∀ r', (r' < S ∨ S + 4 ≤ r') → ((ceilLogW b N T S).exec inp s).regs r' = s.regs r') ∧
    ((ceilLogW b N T S).exec inp s).mem = s.mem ∧
    ((ceilLogW b N T S).exec inp s).cur = s.cur ∧
    ((ceilLogW b N T S).exec inp s).out = s.out ∧
    (ceilLogW b N T S).cost inp B s ≤ (7 * s.regs T + 9) * kappa B (RAM.bits M) := by
  obtain ⟨f1, f2, f3, -, -, -, f7⟩ := floorLogW_spec inp B b N T S s M hb hN hT h2 hlog hM
  set bq := s.regs b with hbq
  set n := s.regs N with hn
  set L := Nat.log bq n with hL
  set s1 := (floorLogW b N T S).exec inp s with hs1
  have eb : s1.regs b = bq := f3 b (Or.inl hb)
  have eN : s1.regs N = n := f3 N (Or.inl hN)
  have hPle : bq ^ L ≤ n + 1 := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · have : L = 0 := by rw [hL, h0]; simp
      rw [this]; simp
    · have := Nat.pow_log_le_self bq h0.ne'
      rw [← hL] at this; omega
  have hprod : bq ^ L * bq ≤ (n + 1) * bq := Nat.mul_le_mul_right _ hPle
  have hexp : (n + 2) * (bq + 1) = (n + 1) * bq + bq + n + 2 := by ring
  have hn1 : n + 1 ≤ (n + 1) * bq := Nat.le_mul_of_pos_right _ (by omega)
  have hex : (ceilLogW b N T S).exec inp s = (seqs [ar .lt (S + 3) (S + 1) N,
    .ifz (S + 3) .skip (seqs [ar .mul (S + 1) (S + 1) b, lit (S + 3) 1, ar .add S S (S + 3)])]).exec
      inp s1 := rfl
  have hco : (ceilLogW b N T S).cost inp B s = (floorLogW b N T S).cost inp B s +
      (seqs [ar .lt (S + 3) (S + 1) N,
    .ifz (S + 3) .skip (seqs [ar .mul (S + 1) (S + 1) b, lit (S + 3) 1, ar .add S S (S + 3)])]).cost
      inp B s1 := rfl
  refine ⟨?_, ?_, ceilLogW_frame inp b N T S s, exec_mem_of_stores inp _ rfl s,
    exec_cur_of_reads inp _ rfl s, exec_out_of_emits inp _ rfl s, ?_⟩
  · rw [hex]
    by_cases hlt : bq ^ L < n
    · have : ceilLog bq n = L + 1 := by simp [ceilLog, floorLog, ← hL, not_le.mpr hlt]
      rw [this]
      simp (disch := omega) [upd_ne, upd_eq, f1, f2, eN, hlt]
    · have : ceilLog bq n = L := by simp [ceilLog, floorLog, ← hL, not_lt.mp hlt]
      rw [this]
      simp (disch := omega) [upd_ne, upd_eq, f1, f2, eN, hlt]
  · rw [hex]
    by_cases hlt : bq ^ L < n
    · have : ceilLog bq n = L + 1 := by simp [ceilLog, floorLog, ← hL, not_le.mpr hlt]
      rw [this]
      simp (disch := omega) [upd_ne, upd_eq, f1, f2, eN, eb, hlt, pow_succ]
    · have : ceilLog bq n = L := by simp [ceilLog, floorLog, ← hL, not_lt.mp hlt]
      rw [this]
      simp (disch := omega) [upd_ne, upd_eq, f1, f2, eN, hlt]
  · rw [hco]
    have hLT : L ≤ s.regs T := hlog
    have e1 := kappa_bits_le B (a := bq ^ L + n) (M := M) (by omega)
    have e2 := kappa_bits_le B (a := (1 : ℕ)) (M := M) (by omega)
    have e3 := kappa_bits_le B (a := (0 : ℕ)) (M := M) (by omega)
    have e4 := kappa_bits_le B (a := bq ^ L + bq) (M := M) (by omega)
    have e5 := kappa_bits_le B (a := L + 1) (M := M) (by omega)
    have hy : (7 * s.regs T + 9) * kappa B (RAM.bits M) =
        (7 * s.regs T + 4) * kappa B (RAM.bits M) + 5 * kappa B (RAM.bits M) := by ring
    by_cases hlt : bq ^ L < n
    · simp (disch := omega) only [cost_seqs_cons, cost_seqs_nil, cost_ar, cost_ifz, cost_lit,
        cost_skip, exec_seqs_cons, exec_ar, exec_lit, HS.setR_regs, upd_ne, upd_eq, f1, f2, eN, eb,
        arith_lt, arith_mul, hlt, if_true, one_ne_zero, if_false]
      omega
    · simp (disch := omega) only [cost_seqs_cons, cost_seqs_nil, cost_ar, cost_ifz, cost_lit,
        cost_skip, exec_seqs_cons, exec_ar, exec_lit, HS.setR_regs, upd_ne, upd_eq, f1, f2, eN, eb,
        arith_lt, arith_mul, hlt, if_true, if_false]
      omega

/-! ### The short length `ρ = shortLength q t h` -/

end Logs

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.ceilLogW_spec_oai := @EditMulticoloring.Dev.Ram.ceilLogW_spec_oai
