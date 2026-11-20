-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.paramsW_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:37:06.33014+00:00
-- url     : https://prove2.me/submissions/5ca982a7-f324-409a-a5c1-01487d74d545

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Construction
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000
import Theorems.Thm_EditMulticoloring_Dev_Ram_kappa_bits_le
import Theorems.Thm_EditMulticoloring_Dev_Ram_pA_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_pPrime_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_powW_spec
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

theorem exec_cur_of_reads (c : Cmd) (h : c.reads = false) (s : HS) :
    (c.exec inp s).cur = s.cur := by
  induction c generalizing s with
  | prim p => cases p <;> simp_all [Cmd.reads, Cmd.exec, Prim.exec]
  | seq c₁ c₂ ih₁ ih₂ =>
    simp only [Cmd.reads, Bool.or_eq_false_iff] at h
    simp [ih₁ h.1, ih₂ h.2]
  | ifz a c₁ c₂ ih₁ ih₂ =>
    simp only [Cmd.reads, Bool.or_eq_false_iff] at h
    simp only [exec_ifz]; split_ifs
    · exact ih₁ h.1 s
    · exact ih₂ h.2 s
  | loop a c ih =>
    simp only [Cmd.reads] at h
    rw [exec_loop]
    exact iterate_induct (fun t => t.cur = s.cur) (fun t ht => (ih h t).trans ht) _ _ rfl
  | skip => rfl

theorem exec_out_of_emits (c : Cmd) (h : c.emits = false) (s : HS) :
    (c.exec inp s).out = s.out := by
  induction c generalizing s with
  | prim p => cases p <;> simp_all [Cmd.emits, Cmd.exec, Prim.exec]
  | seq c₁ c₂ ih₁ ih₂ =>
    simp only [Cmd.emits, Bool.or_eq_false_iff] at h
    simp [ih₁ h.1, ih₂ h.2]
  | ifz a c₁ c₂ ih₁ ih₂ =>
    simp only [Cmd.emits, Bool.or_eq_false_iff] at h
    simp only [exec_ifz]; split_ifs
    · exact ih₁ h.1 s
    · exact ih₂ h.2 s
  | loop a c ih =>
    simp only [Cmd.emits] at h
    rw [exec_loop]
    exact iterate_induct (fun t => t.out = s.out) (fun t ht => (ih h t).trans ht) _ _ rfl
  | skip => rfl

theorem exec_mem_of_stores (c : Cmd) (h : c.stores = false) (s : HS) :
    (c.exec inp s).mem = s.mem := by
  induction c generalizing s with
  | prim p => cases p <;> simp_all [Cmd.stores, Cmd.exec, Prim.exec]
  | seq c₁ c₂ ih₁ ih₂ =>
    simp only [Cmd.stores, Bool.or_eq_false_iff] at h
    simp [ih₁ h.1, ih₂ h.2]
  | ifz a c₁ c₂ ih₁ ih₂ =>
    simp only [Cmd.stores, Bool.or_eq_false_iff] at h
    simp only [exec_ifz]; split_ifs
    · exact ih₁ h.1 s
    · exact ih₂ h.2 s
  | loop a c ih =>
    simp only [Cmd.stores] at h
    rw [exec_loop]
    exact iterate_induct (fun t => t.mem = s.mem) (fun t ht => (ih h t).trans ht) _ _ rfl
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

theorem log_le_of_pos {b n : ℕ} (hb : 2 ≤ b) : Nat.log b n ≤ n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have h1 := Nat.pow_log_le_self b h.ne'
    have h2 : Nat.log b n < b ^ Nat.log b n := Nat.lt_pow_self (by omega)
    omega

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

theorem ceilLogW_spec (b N T S : ℕ) (s : HS) (M : ℕ) (hb : b < S) (hN : N < S) (hT : T < S)
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

theorem radW_frame (q t lR S : ℕ) (s : HS) (r' : ℕ) (h : r' < S ∨ S + 3 ≤ r') :
    ((radW q t lR S).exec inp s).regs r' = s.regs r' := by
  apply exec_regs_of_not_mem
  simp only [radW, powW, seqs, Cmd.wregs, lit, ar, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, not_or, not_false_eq_true, and_true, true_and]
  omega

theorem radiusBound_mono (q s : ℕ) {m m' : ℕ} (h : m ≤ m') : radiusBound q s m ≤ radiusBound q s m' := by
  unfold radiusBound
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  apply Nat.mul_le_mul_left
  omega

theorem radW_spec (q t lR S : ℕ) (s : HS) (M : ℕ) (hl : lR < S) (hq : 1 ≤ q)
    (hM : radiusBound q (2 * t) (s.regs lR) + 2 * q * (s.regs lR + 2 * t + 1) + 2 * q + 2 * t + 2 ≤ M) :
    ((radW q t lR S).exec inp s).regs S = radiusBound q (2 * t) (s.regs lR) ∧
    (∀ r', (r' < S ∨ S + 3 ≤ r') → ((radW q t lR S).exec inp s).regs r' = s.regs r') ∧
    ((radW q t lR S).exec inp s).mem = s.mem ∧
    ((radW q t lR S).exec inp s).cur = s.cur ∧
    ((radW q t lR S).exec inp s).out = s.out ∧
    (radW q t lR S).cost inp B s ≤ (4 * t + 11) * kappa B (RAM.bits M) := by
  set l := s.regs lR with hl'
  set s1 := (seqs [lit S (2 * t + 1), ar .add S lR S, lit (S + 1) (2 * q), ar .mul S S (S + 1),
    lit (S + 1) (2 * t)]).exec inp s with hs1
  set base := (l + (2 * t + 1)) * (2 * q) with hbase
  have e0 : s1.regs S = base := by simp (disch := omega) [hs1, upd_ne, hbase, hl']
  have e1 : s1.regs (S + 1) = 2 * t := by simp (disch := omega) [hs1, upd_ne]
  have hb1 : 1 ≤ base := by rw [hbase]; nlinarith
  have hR : radiusBound q (2 * t) l = (2 * t + 1) * base ^ (2 * t) := by
    rw [radiusBound, hbase]; ring_nf
  have hbR : base ^ (2 * t) ≤ radiusBound q (2 * t) l := by rw [hR]; nlinarith
  have hbase' : base = 2 * q * (l + 2 * t + 1) := by rw [hbase]; ring
  obtain ⟨p1, p2, -, -, -, p6⟩ := powW_spec inp B S (S + 1) (S + 2) s1 M (by omega) (by omega)
    (by rw [e0]; exact hb1) (by rw [e0, e1]; omega)
  set s2 := (powW S (S + 1) (S + 2)).exec inp s1 with hs2
  have hex : (radW q t lR S).exec inp s = (seqs [lit (S + 1) (2 * t + 1),
    ar .mul S (S + 2) (S + 1)]).exec inp s2 := rfl
  have hco : (radW q t lR S).cost inp B s = (seqs [lit S (2 * t + 1), ar .add S lR S,
      lit (S + 1) (2 * q), ar .mul S S (S + 1), lit (S + 1) (2 * t)]).cost inp B s +
      ((powW S (S + 1) (S + 2)).cost inp B s1 + (seqs [lit (S + 1) (2 * t + 1),
    ar .mul S (S + 2) (S + 1)]).cost inp B s2) := rfl
  have f2 : s2.regs (S + 2) = base ^ (2 * t) := by rw [p1, e0, e1]
  refine ⟨?_, radW_frame inp q t lR S s, exec_mem_of_stores inp _ rfl s,
    exec_cur_of_reads inp _ rfl s, exec_out_of_emits inp _ rfl s, ?_⟩
  · rw [hex]; simp (disch := omega) only [exec_seqs_cons, exec_seqs_nil, exec_lit, exec_ar,
      HS.setR_regs, upd_ne, upd_eq, f2, arith_mul]
    rw [hR]; ring
  · rw [hco]
    rw [e1] at p6
    simp (disch := omega) only [cost_seqs_cons, cost_seqs_nil, cost_ar, cost_lit, exec_seqs_cons,
      exec_ar, exec_lit, HS.setR_regs, upd_ne, upd_eq, f2, arith_add, arith_mul, hl']
    have hb2 : l + 2 * t + 1 ≤ 2 * q * (l + 2 * t + 1) := by nlinarith
    have k1 := kappa_bits_le B (a := 2 * t + 1) (M := M) (by omega)
    have k2 := kappa_bits_le B (a := l + (2 * t + 1)) (M := M) (by omega)
    have k3 := kappa_bits_le B (a := 2 * q) (M := M) (by omega)
    have k4 := kappa_bits_le B (a := l + (2 * t + 1) + 2 * q) (M := M) (by omega)
    have k5 := kappa_bits_le B (a := 2 * t) (M := M) (by omega)
    have k6 := kappa_bits_le B (a := base ^ (2 * t) + (2 * t + 1)) (M := M) (by omega)
    rw [← hl']
    have hy : (4 * t + 11) * kappa B (RAM.bits M) =
        (2 * (2 * t) + 3) * kappa B (RAM.bits M) + 8 * kappa B (RAM.bits M) := by ring
    omega

/-! ### The short length `ρ = shortLength q t h` -/

theorem shortLength_eq_of {q t h ρ : ℕ} (hc : rhoCond q t h ρ) (hmin : ∀ l < ρ, ¬ rhoCond q t h l) :
    shortLength q t h = ρ := by
  unfold shortLength
  apply le_antisymm (Nat.sInf_le hc)
  have hne : Set.Nonempty {l : ℕ | h ≤ l ∧ q ^ h * radiusBound q (2 * t) l ≤ q ^ l} := ⟨ρ, hc⟩
  have hm := Nat.sInf_mem hne
  by_contra hlt
  exact hmin _ (by omega) hm

theorem rhoTest_frame (hR S : ℕ) (s : HS) (r' : ℕ) (h0 : r' ≠ S) (h1 : r' ≠ S + 1) (h7 : r' ≠ S + 7)
    (h8 : r' ≠ S + 8) : ((rhoTest hR S).exec inp s).regs r' = s.regs r' := by
  apply exec_regs_of_not_mem
  simp only [rhoTest, seqs, Cmd.wregs, lit, ar, cp, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, not_or, not_false_eq_true, and_true, true_and]
  omega

theorem rhoTest_spec (hR S : ℕ) (s : HS) (M : ℕ) (hh : hR < S)
    (hM : s.regs (S + 2) + s.regs (S + 6) + s.regs (S + 4) + s.regs hR + s.regs (S + 1) + 1 ≤ M) :
    ((rhoTest hR S).exec inp s).regs S =
      (if s.regs (S + 1) = 0 ∧ ¬ s.regs (S + 2) < s.regs (S + 6) ∧ ¬ s.regs (S + 4) < s.regs hR
        then s.regs (S + 4) else s.regs S) ∧
    ((rhoTest hR S).exec inp s).regs (S + 1) =
      (if s.regs (S + 1) = 0 ∧ ¬ s.regs (S + 2) < s.regs (S + 6) ∧ ¬ s.regs (S + 4) < s.regs hR
        then 1 else s.regs (S + 1)) ∧
    (rhoTest hR S).cost inp B s ≤ 7 * kappa B (RAM.bits M) := by
  have e1 := kappa_bits_le B (a := s.regs (S + 1)) (M := M) (by omega)
  have e2 := kappa_bits_le B (a := s.regs (S + 2) + s.regs (S + 6)) (M := M) (by omega)
  have e3 := kappa_bits_le B (a := s.regs (S + 4) + s.regs hR) (M := M) (by omega)
  have e4 := kappa_bits_le B (a := s.regs (S + 4)) (M := M) (by omega)
  have e5 := kappa_bits_le B (a := 1) (M := M) (by omega)
  have e6 := kappa_bits_le B (a := 0) (M := M) (by omega)
  by_cases hf : s.regs (S + 1) = 0
  · by_cases c1 : s.regs (S + 2) < s.regs (S + 6)
    · simp (disch := omega) only [rhoTest, exec_ifz, exec_seqs_cons, exec_seqs_nil, exec_ar,
        exec_cp, exec_lit, exec_skip, HS.setR_regs, upd_ne, upd_eq, hf, c1, arith_lt, if_true,
        if_false, one_ne_zero, cost_ifz, cost_seqs_cons, cost_seqs_nil, cost_ar, cost_cp, cost_lit,
        cost_skip, not_true_eq_false, false_and, and_false, true_and]
      omega
    · by_cases c2 : s.regs (S + 4) < s.regs hR
      · simp (disch := omega) only [rhoTest, exec_ifz, exec_seqs_cons, exec_seqs_nil, exec_ar,
          exec_cp, exec_lit, exec_skip, HS.setR_regs, upd_ne, upd_eq, hf, c1, c2, arith_lt, if_true,
          if_false, one_ne_zero, cost_ifz, cost_seqs_cons, cost_seqs_nil, cost_ar, cost_cp, cost_lit,
          cost_skip, not_true_eq_false, false_and, and_false, true_and, not_false_eq_true]
        omega
      · simp (disch := omega) only [rhoTest, exec_ifz, exec_seqs_cons, exec_seqs_nil, exec_ar,
          exec_cp, exec_lit, exec_skip, HS.setR_regs, upd_ne, upd_eq, hf, c1, c2, arith_lt, if_true,
          if_false, one_ne_zero, cost_ifz, cost_seqs_cons, cost_seqs_nil, cost_ar, cost_cp, cost_lit,
          cost_skip, not_true_eq_false, false_and, and_false, true_and, not_false_eq_true, and_self]
        omega
  · simp (disch := omega) only [rhoTest, exec_ifz, exec_seqs_cons, exec_seqs_nil, exec_ar,
      exec_cp, exec_lit, exec_skip, HS.setR_regs, upd_ne, upd_eq, hf, arith_lt, if_true,
      if_false, one_ne_zero, cost_ifz, cost_seqs_cons, cost_seqs_nil, cost_ar, cost_cp, cost_lit,
      cost_skip, false_and, and_false, true_and]
    omega

theorem rhoBody_frame (q t hR qhR S : ℕ) (s : HS) (r' : ℕ) (h0 : r' ≠ S) (h1 : r' ≠ S + 1)
    (h2 : r' ≠ S + 2) (h : r' < S + 6 ∨ S + 9 ≤ r') :
    ((rhoBody q t hR qhR S).exec inp s).regs r' = s.regs r' := by
  apply exec_regs_of_not_mem
  simp only [rhoBody, rhoTest, radW, powW, seqs, Cmd.wregs, lit, ar, cp, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, and_true, true_and]
  omega

theorem rhoW_frame (q t nR hR qhR S : ℕ) (s : HS) (r' : ℕ) (h : r' < S ∨ S + 9 ≤ r') :
    ((rhoW q t nR hR qhR S).exec inp s).regs r' = s.regs r' := by
  apply exec_regs_of_not_mem
  simp only [rhoW, forLoop, rhoBody, rhoTest, radW, powW, seqs, Cmd.wregs, lit, ar, cp,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true,
    and_true, true_and]
  omega

theorem rhoW_spec (q t nR hR qhR S : ℕ) (s : HS) (M : ℕ) (hn : nR < S) (hh : hR < S)
    (hqh : qhR < S) (hq : 2 ≤ q) (hqhv : s.regs qhR = q ^ s.regs hR)
    (hex : ∃ l ≤ s.regs nR, rhoCond q t (s.regs hR) l)
    (hM : q ^ (s.regs nR + 1) + 2 * (q ^ s.regs hR * radiusBound q (2 * t) (s.regs nR)) +
      2 * q * (s.regs nR + 2 * t + 1) + 2 * q + 2 * t + s.regs hR + s.regs nR + 4 ≤ M) :
    ((rhoW q t nR hR qhR S).exec inp s).regs S = shortLength q t (s.regs hR) ∧
    (∀ r', (r' < S ∨ S + 9 ≤ r') → ((rhoW q t nR hR qhR S).exec inp s).regs r' = s.regs r') ∧
    ((rhoW q t nR hR qhR S).exec inp s).mem = s.mem ∧
    ((rhoW q t nR hR qhR S).exec inp s).cur = s.cur ∧
    ((rhoW q t nR hR qhR S).exec inp s).out = s.out ∧
    (rhoW q t nR hR qhR S).cost inp B s ≤
      ((4 * t + 24) * (s.regs nR + 1) + 8) * kappa B (RAM.bits M) := by
  set n := s.regs nR with hnd
  set h := s.regs hR with hhd
  set s1 := (seqs [lit S 0, lit (S + 1) 0, lit (S + 2) 1, lit (S + 3) 1,
    ar .add (S + 3) nR (S + 3)]).exec inp s with hs1
  have hn3 : s1.regs (S + 3) = n + 1 := by simp (disch := omega) [hs1, upd_ne, hnd]
  have hqh1 : 1 ≤ q ^ h := Nat.one_le_pow _ _ (by omega)
  have hRn : radiusBound q (2 * t) n ≤ q ^ h * radiusBound q (2 * t) n := Nat.le_mul_of_pos_left _ hqh1
  have K := forLoop_spec inp B (S + 4) (S + 3) (S + 5) (rhoBody q t hR qhR S) s1 (by omega) (by omega)
    (fun k st => st.regs (S + 2) = q ^ k ∧ (∀ r', (r' < S ∨ S + 9 ≤ r') → st.regs r' = s.regs r') ∧
      ((st.regs (S + 1) = 0 ∧ ∀ l < k, ¬ rhoCond q t h l) ∨
       (st.regs (S + 1) = 1 ∧ st.regs S < k ∧ rhoCond q t h (st.regs S) ∧
         ∀ l < st.regs S, ¬ rhoCond q t h l)))
    (fun _ => (4 * t + 21) * kappa B (RAM.bits M))
    ⟨by simp (disch := omega) [hs1, upd_ne], fun r' h => by simp (disch := omega) [hs1, upd_ne],
      Or.inl ⟨by simp (disch := omega) [hs1, upd_ne], fun l hl => absurd hl (Nat.not_lt_zero _)⟩⟩
    (by
      intro k hk st ⟨hpow, hr, hinv⟩ hi
      rw [hn3] at hk
      have hkn : k ≤ n := by omega
      have eh : st.regs hR = h := hr hR (Or.inl hh)
      have eqh : st.regs qhR = q ^ h := by rw [hr qhR (Or.inl hqh), hqhv]
      have hRk : radiusBound q (2 * t) k ≤ radiusBound q (2 * t) n := radiusBound_mono q _ hkn
      have hlin : 2 * q * (k + 2 * t + 1) ≤ 2 * q * (n + 2 * t + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      obtain ⟨d1, d2, -, -, -, d6⟩ := radW_spec inp B q t (S + 4) (S + 6) st M (by omega) (by omega)
        (by rw [hi]; omega)
      rw [hi] at d1
      set s2 := (radW q t (S + 4) (S + 6)).exec inp st with hs2
      have f4 : s2.regs (S + 4) = k := by rw [d2 _ (by omega), hi]
      have f2 : s2.regs (S + 2) = q ^ k := by rw [d2 _ (by omega), hpow]
      have f1 : s2.regs (S + 1) = st.regs (S + 1) := d2 _ (by omega)
      have f0 : s2.regs S = st.regs S := d2 _ (by omega)
      have fh : s2.regs hR = h := by rw [d2 _ (by omega), eh]
      have fqh : s2.regs qhR = q ^ h := by rw [d2 _ (by omega), eqh]
      set X := q ^ h * radiusBound q (2 * t) k with hX
      have hXn : X ≤ q ^ h * radiusBound q (2 * t) n := Nat.mul_le_mul_left _ hRk
      set s3 := s2.setR (S + 6) X with hs3
      have hqk : q ^ k ≤ q ^ n := Nat.pow_le_pow_right (by omega) hkn
      have hqn : q ^ n * q = q ^ (n + 1) := (pow_succ q n).symm
      have hqk1 : q ^ k * q ≤ q ^ (n + 1) := by rw [← hqn]; exact Nat.mul_le_mul_right _ hqk
      have hqn1 : q ^ n ≤ q ^ (n + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have hqk' : q ^ k ≤ q ^ (n + 1) := hqk.trans hqn1
      have hflag : st.regs (S + 1) ≤ 1 := by
        rcases hinv with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
      obtain ⟨t1, t2, t3⟩ := rhoTest_spec inp B hR S s3 M hh (by
        simp (disch := omega) only [hs3, HS.setR_regs, upd_ne, upd_eq, f2, f4, fh, f1]
        omega)
      simp (disch := omega) only [hs3, HS.setR_regs, upd_ne, upd_eq, f2, f4, fh, f1, f0] at t1 t2
      set s4 := (rhoTest hR S).exec inp s3 with hs4
      have g2 : s4.regs (S + 2) = q ^ k := by
        rw [hs4, rhoTest_frame inp hR S s3 _ (by omega) (by omega) (by omega) (by omega)]
        simp (disch := omega) [hs3, upd_ne, f2]
      have hex' : (rhoBody q t hR qhR S).exec inp st = ((s4.setR (S + 7) q).setR (S + 2)
          (s4.regs (S + 2) * q)) := by
        show (seqs [ar .mul (S + 6) qhR (S + 6), rhoTest hR S,
          lit (S + 7) q, ar .mul (S + 2) (S + 2) (S + 7)]).exec inp s2 = _
        simp (disch := omega) only [exec_seqs_cons, exec_seqs_nil, exec_ar, exec_lit, arith_mul,
          HS.setR_regs, upd_ne, upd_eq, fqh]
        rw [show s2.setR (S + 6) (q ^ h * s2.regs (S + 6)) = s3 by rw [hs3, d1]]
      have hco : (rhoBody q t hR qhR S).cost inp B st = (radW q t (S + 4) (S + 6)).cost inp B st +
          (seqs [ar .mul (S + 6) qhR (S + 6), rhoTest hR S, lit (S + 7) q,
            ar .mul (S + 2) (S + 2) (S + 7)]).cost inp B s2 := rfl
      have hs3' : (ar .mul (S + 6) qhR (S + 6)).exec inp s2 = s3 := by
        rw [hs3, exec_ar, fqh, d1, arith_mul]
      have hR1 : 0 < radiusBound q (2 * t) n :=
        Nat.mul_pos (by omega) (Nat.pow_pos (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)))
      have hqhR : q ^ h ≤ q ^ h * radiusBound q (2 * t) n := Nat.le_mul_of_pos_right _ hR1
      refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩
      · rw [rhoBody_frame inp q t hR qhR S st _ (by omega) (by omega) (by omega) (by omega), hi]
      · rw [hex']; simp (disch := omega) only [HS.setR_regs, upd_ne, upd_eq, g2, pow_succ]
      · intro r' hr'
        rw [hex']
        simp (disch := omega) only [HS.setR_regs, upd_ne]
        rw [hs4, rhoTest_frame inp hR S s3 _ (by omega) (by omega) (by omega) (by omega), hs3]
        simp (disch := omega) only [HS.setR_regs, upd_ne]
        rw [hs2, radW_frame inp q t (S + 4) (S + 6) st _ (by omega)]
        exact hr r' hr'
      · rw [hex']
        simp (disch := omega) only [HS.setR_regs, upd_ne]
        rw [t1, t2]
        rcases hinv with ⟨h0, hno⟩ | ⟨h1, hlt, hc, hmin⟩
        · by_cases hck : rhoCond q t h k
          · have hc' : st.regs (S + 1) = 0 ∧ ¬ q ^ k < X ∧ ¬ k < h := ⟨h0, by
              have := hck.2; rw [← hX] at this; omega, by have := hck.1; omega⟩
            rw [if_pos hc', if_pos hc']
            exact Or.inr ⟨rfl, by omega, hck, hno⟩
          · have hc' : ¬ (st.regs (S + 1) = 0 ∧ ¬ q ^ k < X ∧ ¬ k < h) := by
              rintro ⟨-, a1, a2⟩
              exact hck ⟨by omega, by rw [← hX]; omega⟩
            rw [if_neg hc', if_neg hc']
            refine Or.inl ⟨h0, fun l hl => ?_⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl | hl
            · exact hno l hl
            · rw [hl]; exact hck
        · have hc' : ¬ (st.regs (S + 1) = 0 ∧ ¬ q ^ k < X ∧ ¬ k < h) := by
            rintro ⟨a0, -, -⟩; omega
          rw [if_neg hc', if_neg hc']
          exact Or.inr ⟨h1, by omega, hc, hmin⟩
      · rw [hco, cost_seqs_cons, hs3', cost_seqs_cons, ← hs4, cost_seqs_cons, cost_seqs_cons,
          cost_seqs_nil]
        simp (disch := omega) only [cost_ar, cost_lit, exec_lit, HS.setR_regs, upd_ne, upd_eq, fqh,
          d1, g2]
        have e1 := kappa_bits_le B (a := q ^ h + radiusBound q (2 * t) k) (M := M) (by omega)
        have e2 := kappa_bits_le B (a := q) (M := M) (by omega)
        have e3 := kappa_bits_le B (a := q ^ k + q) (M := M) (by omega)
        have hy : (4 * t + 21) * kappa B (RAM.bits M) =
          (4 * t + 11) * kappa B (RAM.bits M) + 10 * kappa B (RAM.bits M) := by ring
        omega)
  obtain ⟨⟨k1, k2, k3⟩, k4⟩ := K
  simp only [hn3] at k1 k2 k3 k4
  have hex2 : (rhoW q t nR hR qhR S).exec inp s =
      (forLoop (S + 4) (S + 3) (S + 5) (rhoBody q t hR qhR S)).exec inp s1 := rfl
  have hco2 : (rhoW q t nR hR qhR S).cost inp B s = (seqs [lit S 0, lit (S + 1) 0, lit (S + 2) 1,
      lit (S + 3) 1, ar .add (S + 3) nR (S + 3)]).cost inp B s +
      (forLoop (S + 4) (S + 3) (S + 5) (rhoBody q t hR qhR S)).cost inp B s1 := rfl
  refine ⟨?_, rhoW_frame inp q t nR hR qhR S s, exec_mem_of_stores inp _ rfl s,
    exec_cur_of_reads inp _ rfl s, exec_out_of_emits inp _ rfl s, ?_⟩
  · rw [hex2]
    rcases k3 with ⟨-, hno⟩ | ⟨-, -, hc, hmin⟩
    · obtain ⟨l, hl, hcl⟩ := hex
      exact absurd hcl (hno l (by omega))
    · exact (shortLength_eq_of hc hmin).symm
  · rw [hco2]
    simp (disch := omega) only [cost_seqs_cons, cost_seqs_nil, cost_lit, cost_ar, exec_seqs_cons,
      exec_lit, HS.setR_regs, upd_ne, upd_eq] at k4 ⊢
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at k4
    have e1 := kappa_bits_le B (a := 0) (M := M) (by omega)
    have e2 := kappa_bits_le B (a := 1) (M := M) (by omega)
    have e3 := kappa_bits_le B (a := n + 1) (M := M) (by omega)
    rw [← hnd]
    have hy : ((4 * t + 24) * (n + 1) + 8) * kappa B (RAM.bits M) =
      3 * (n + 1 + 1) * kappa B (RAM.bits M) + (n + 1) * ((4 * t + 21) * kappa B (RAM.bits M)) +
        5 * kappa B (RAM.bits M) + 0 := by ring
    have hz : 3 * (n + 1 + 1) * kappa B (RAM.bits (n + 1)) ≤ 3 * (n + 1 + 1) * kappa B (RAM.bits M) :=
      Nat.mul_le_mul_left _ e3
    omega

end Logs

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamParams4
/-!
# Part P (q379): the parameters, part A (`r, K, b, Q, B, L, W`) and part F (`f, J, h₁`)

Output block `O`: `O+0 r, O+1 K, O+2 b, O+3 Q, O+4 B, O+5 L, O+6 W = b + 1,
O+7 f = floorLog q (L / 2), O+8 J, O+9 h₁, O+10 h₂, O+11 h, O+12 q^h, O+13 ρ, O+14 q^ρ,
O+15 m, O+16 k`; temporaries `O+17 .. O+22`; subroutine scratch from `O+23` (to `O+48`).
Here `b = ceilLog 2 (r * K + 1)` (so `Q = 2 ^ b`, `B = 2 b`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

section PartF
variable (inp : ℕ → ℕ) (B : ℕ)

theorem ceilLog_le_succ (q N : ℕ) (hq : 2 ≤ q) : ceilLog q N ≤ N + 1 := by
  have := log_le_of_pos (n := N) hq
  show (if N ≤ q ^ Nat.log q N then Nat.log q N else Nat.log q N + 1) ≤ N + 1
  split_ifs <;> omega

theorem pow_log_le_succ (q N : ℕ) : q ^ Nat.log q N ≤ N + 1 := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp
  · have := Nat.pow_log_le_self q h.ne'; omega

theorem pF_spec (q O : ℕ) (s : HS) (M : ℕ) (hq : 2 ≤ q)
    (hM : (s.regs (O + 5) + 2) * (q + 1) + s.regs (O + 5) ≤ M) :
    ((pF q O).exec inp s).regs (O + 7) = Nat.log q (s.regs (O + 5) / 2) ∧
    ((pF q O).exec inp s).regs (O + 8) = q ^ Nat.log q (s.regs (O + 5) / 2) ∧
    ((pF q O).exec inp s).regs (O + 9) = ceilLog q (s.regs (O + 5)) ∧
    (∀ r', (r' < O + 7 ∨ (O + 10 ≤ r' ∧ r' < O + 17) ∨ O + 49 ≤ r') →
      ((pF q O).exec inp s).regs r' = s.regs r') ∧
    ((pF q O).exec inp s).mem = s.mem ∧
    ((pF q O).exec inp s).cur = s.cur ∧
    ((pF q O).exec inp s).out = s.out ∧
    (pF q O).cost inp B s ≤ (11 * s.regs (O + 5) + 19) * kappa B (RAM.bits M) := by
  set L := s.regs (O + 5) with hLd
  set s1 := (seqs [lit (O + 17) q, lit (O + 19) 2, ar .div (O + 18) (O + 5) (O + 19)]).exec inp s
    with hs1
  have a17 : s1.regs (O + 17) = q := by
    simp (disch := omega) only [hs1, exec_seqs_cons, exec_seqs_nil, exec_lit, exec_ar, HS.setR_regs,
      upd_ne, upd_eq]
  have a18 : s1.regs (O + 18) = L / 2 := by
    simp (disch := omega) only [hs1, exec_seqs_cons, exec_seqs_nil, exec_lit, exec_ar, HS.setR_regs,
      upd_ne, upd_eq, arith_div, hLd]
  have afr : ∀ r', r' ≠ O + 17 → r' ≠ O + 18 → r' ≠ O + 19 → s1.regs r' = s.regs r' :=
    fun r' a1 a2 a3 => by
      simp (disch := omega) only [hs1, exec_seqs_cons, exec_seqs_nil, exec_lit, exec_ar,
        HS.setR_regs, upd_ne]
  have hL2 : L / 2 ≤ L := Nat.div_le_self _ _
  have hqM : (L / 2 + 2) * (q + 1) ≤ (L + 2) * (q + 1) := Nat.mul_le_mul_right _ (by omega)
  obtain ⟨f1, f2, f3, -, -, -, f7⟩ := floorLogW_spec inp B (O + 17) (O + 18) (O + 18) (O + 23) s1 M
    (by omega) (by omega) (by omega) (by rw [a17]; exact hq)
    (by rw [a17, a18]; exact log_le_of_pos hq) (by rw [a17, a18]; omega)
  rw [a17, a18] at f1 f2
  rw [a18] at f7
  set s2 := (floorLogW (O + 17) (O + 18) (O + 18) (O + 23)).exec inp s1 with hs2
  set f := Nat.log q (L / 2) with hf
  have hfL : f ≤ L := (log_le_of_pos hq).trans hL2
  have hJ : q ^ f ≤ L + 1 := (pow_log_le_succ q _).trans (by omega)
  set s3 := (seqs [cp (O + 7) (O + 23), cp (O + 8) (O + 24)]).exec inp s2 with hs3
  have b7 : s3.regs (O + 7) = f := by
    simp (disch := omega) only [hs3, exec_seqs_cons, exec_seqs_nil, exec_cp, HS.setR_regs, upd_ne,
      upd_eq, f1]
  have b8 : s3.regs (O + 8) = q ^ f := by
    simp (disch := omega) only [hs3, exec_seqs_cons, exec_seqs_nil, exec_cp, HS.setR_regs, upd_ne,
      upd_eq, f2]
  have bfr : ∀ r', r' ≠ O + 7 → r' ≠ O + 8 → s3.regs r' = s2.regs r' := fun r' a1 a2 => by
    simp (disch := omega) only [hs3, exec_seqs_cons, exec_seqs_nil, exec_cp, HS.setR_regs, upd_ne]
  have b17 : s3.regs (O + 17) = q := by
    rw [bfr _ (by omega) (by omega), f3 _ (by omega), a17]
  have b5 : s3.regs (O + 5) = L := by
    rw [bfr _ (by omega) (by omega), f3 _ (by omega), afr _ (by omega) (by omega) (by omega)]
  obtain ⟨c1, -, c3, -, -, -, c7⟩ := ceilLogW_spec inp B (O + 17) (O + 5) (O + 5) (O + 23) s3 M
    (by omega) (by omega) (by omega) (by rw [b17]; exact hq)
    (by rw [b17, b5]; exact log_le_of_pos hq) (by rw [b17, b5]; omega)
  rw [b17, b5] at c1
  rw [b5] at c7
  set s4 := (ceilLogW (O + 17) (O + 5) (O + 5) (O + 23)).exec inp s3 with hs4
  have hex : (pF q O).exec inp s = s4.setR (O + 9) (s4.regs (O + 23)) := rfl
  have hco : (pF q O).cost inp B s =
      (seqs [lit (O + 17) q, lit (O + 19) 2, ar .div (O + 18) (O + 5) (O + 19)]).cost inp B s +
      ((floorLogW (O + 17) (O + 18) (O + 18) (O + 23)).cost inp B s1 +
      ((seqs [cp (O + 7) (O + 23), cp (O + 8) (O + 24)]).cost inp B s2 +
      ((ceilLogW (O + 17) (O + 5) (O + 5) (O + 23)).cost inp B s3 +
        kappa B (RAM.bits (s4.regs (O + 23)))))) := rfl
  have hcl := ceilLog_le_succ q L hq
  have hLq : L + 2 ≤ (L + 2) * (q + 1) := Nat.le_mul_of_pos_right _ (by omega)
  clear_value s1 s2 s3 s4
  have k1 : (seqs [lit (O + 17) q, lit (O + 19) 2, ar .div (O + 18) (O + 5) (O + 19)]).cost inp B s ≤
      3 * kappa B (RAM.bits M) := by
    simp (disch := omega) only [cost_seqs_cons, cost_seqs_nil, cost_lit, cost_ar, exec_lit,
      HS.setR_regs, upd_ne, upd_eq, ← hLd]
    have := kappa_bits_le B (a := q) (M := M) (by nlinarith)
    have := kappa_bits_le B (a := 2) (M := M) (by omega)
    have := kappa_bits_le B (a := L + 2) (M := M) (by omega)
    omega
  have k3 : (seqs [cp (O + 7) (O + 23), cp (O + 8) (O + 24)]).cost inp B s2 ≤
      2 * kappa B (RAM.bits M) := by
    simp (disch := omega) only [cost_seqs_cons, cost_seqs_nil, cost_cp, exec_cp, HS.setR_regs,
      upd_ne, f1, f2]
    have := kappa_bits_le B (a := f) (M := M) (by omega)
    have := kappa_bits_le B (a := q ^ f) (M := M) (by omega)
    omega
  have k5 : kappa B (RAM.bits (s4.regs (O + 23))) ≤ kappa B (RAM.bits M) := by
    rw [c1]; exact kappa_bits_le B (by omega)
  rw [hex]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp (disch := omega) only [HS.setR_regs, upd_ne]; rw [c3 _ (by omega), b7]
  · simp (disch := omega) only [HS.setR_regs, upd_ne]; rw [c3 _ (by omega), b8]
  · simp (disch := omega) only [HS.setR_regs, upd_eq]; exact c1
  · intro r' h
    simp (disch := omega) only [HS.setR_regs, upd_ne]
    rw [c3 _ (by omega), bfr _ (by omega) (by omega), f3 _ (by omega),
      afr _ (by omega) (by omega) (by omega)]
  · show (s4.setR (O + 9) (s4.regs (O + 23))).mem = s.mem
    rw [← hex]; exact exec_mem_of_stores inp _ rfl s
  · rw [← hex]; exact exec_cur_of_reads inp _ rfl s
  · rw [← hex]; exact exec_out_of_emits inp _ rfl s
  · rw [hco]
    have h7 : (7 * (L / 2) + 4) * kappa B (RAM.bits M) ≤ (4 * L + 4) * kappa B (RAM.bits M) :=
      Nat.mul_le_mul_right _ (by omega)
    have hy : (11 * L + 19) * kappa B (RAM.bits M) = 3 * kappa B (RAM.bits M) +
      (4 * L + 4) * kappa B (RAM.bits M) + 2 * kappa B (RAM.bits M) +
      (7 * L + 9) * kappa B (RAM.bits M) + kappa B (RAM.bits M) := by ring
    omega

end PartF

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamParams5
/-!
# Part P (q379): the parameters, part P (prime table, `h₂`, `h`) and part R (`q^h, ρ, q^ρ, m, k`)
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

theorem shortLength_le_of_witness {q t h n : ℕ} (hw : ∃ l ≤ n, rhoCond q t h l) :
    shortLength q t h ≤ n := by
  obtain ⟨l, hl, hc⟩ := hw
  exact (Nat.sInf_le hc).trans hl

section PartR
variable (inp : ℕ → ℕ) (B : ℕ)

theorem pR_spec (q t nR O : ℕ) (s : HS) (M : ℕ) (hq : 2 ≤ q) (hn : nR < O)
    (hw : ∃ l ≤ s.regs nR, rhoCond q t (s.regs (O + 11)) l)
    (hM : pRBound q t (s.regs nR) (s.regs (O + 11)) (s.regs (O + 7)) ≤ M) :
    ((pR q t nR O).exec inp s).regs (O + 12) = q ^ s.regs (O + 11) ∧
    ((pR q t nR O).exec inp s).regs (O + 13) = shortLength q t (s.regs (O + 11)) ∧
    ((pR q t nR O).exec inp s).regs (O + 14) = q ^ shortLength q t (s.regs (O + 11)) ∧
    ((pR q t nR O).exec inp s).regs (O + 15) = s.regs nR - shortLength q t (s.regs (O + 11)) ∧
    ((pR q t nR O).exec inp s).regs (O + 16) =
      s.regs nR - shortLength q t (s.regs (O + 11)) + s.regs (O + 7) ∧
    (∀ r', (r' < O + 12 ∨ O + 49 ≤ r') → ((pR q t nR O).exec inp s).regs r' = s.regs r') ∧
    ((pR q t nR O).exec inp s).mem = s.mem ∧
    ((pR q t nR O).exec inp s).cur = s.cur ∧
    ((pR q t nR O).exec inp s).out = s.out ∧
    (pR q t nR O).cost inp B s ≤
      ((4 * t + 24) * (s.regs nR + 1) + 2 * s.regs (O + 11) + 2 * s.regs nR + 20) *
        kappa B (RAM.bits M) := by
  set n := s.regs nR with hnd
  set hv := s.regs (O + 11) with hhv
  set fv := s.regs (O + 7) with hfv
  set ρ := shortLength q t hv with hρ
  have hρn : ρ ≤ n := shortLength_le_of_witness hw
  have hqρ : q ^ ρ ≤ q ^ (n + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  unfold pRBound at hM
  have hqhR : q ^ hv ≤ q ^ hv * radiusBound q (2 * t) n :=
    Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega)
      (Nat.pow_pos (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega))))
  have h2q : q ≤ 2 * q * (n + 2 * t + 1) := by nlinarith
  have hn2 : n ≤ 2 * q * (n + 2 * t + 1) := by nlinarith
  clear_value ρ
  set s1 := s.setR (O + 17) q with hs1
  have a17 : s1.regs (O + 17) = q := by simp [hs1]
  have afr : ∀ r', r' ≠ O + 17 → s1.regs r' = s.regs r' := fun r' a => by
    simp (disch := omega) [hs1, upd_ne]
  obtain ⟨w1, w2, w3, -, -, w6⟩ := powW_spec inp B (O + 17) (O + 11) (O + 23) s1 M (by omega)
    (by omega) (by rw [a17]; omega) (by rw [a17, afr _ (by omega), ← hhv]; omega)
  rw [a17, afr _ (by omega), ← hhv] at w1
  rw [afr _ (by omega), ← hhv] at w6
  set s2 := (powW (O + 17) (O + 11) (O + 23)).exec inp s1 with hs2
  set s3 := s2.setR (O + 12) (s2.regs (O + 23)) with hs3
  have b12 : s3.regs (O + 12) = q ^ hv := by simp [hs3, w1]
  have bfr : ∀ r', r' ≠ O + 12 → r' ≠ O + 23 → r' ≠ O + 17 → s3.regs r' = s.regs r' :=
    fun r' a1 a2 a3 => by
      simp (disch := omega) only [hs3, HS.setR_regs, upd_ne]
      rw [w2 _ a2, afr _ a3]
  have b17 : s3.regs (O + 17) = q := by
    simp (disch := omega) only [hs3, HS.setR_regs, upd_ne]; rw [w2 _ (by omega), a17]
  obtain ⟨r1, r2, r3, -, -, r6⟩ := rhoW_spec inp B q t nR (O + 11) (O + 12) (O + 23) s3 M
    (by omega) (by omega) (by omega) hq (by rw [b12, bfr _ (by omega) (by omega) (by omega)])
    (by rw [bfr _ (by omega) (by omega) (by omega), bfr _ (by omega) (by omega) (by omega)]
        exact hw)
    (by rw [bfr _ (by omega) (by omega) (by omega), bfr _ (by omega) (by omega) (by omega), ← hnd,
          ← hhv]
        omega)
  rw [bfr _ (by omega) (by omega) (by omega), ← hhv] at r1
  rw [bfr _ (by omega) (by omega) (by omega), ← hnd] at r6
  set s4 := (rhoW q t nR (O + 11) (O + 12) (O + 23)).exec inp s3 with hs4
  set s5 := s4.setR (O + 13) (s4.regs (O + 23)) with hs5
  have c13 : s5.regs (O + 13) = ρ := by simp [hs5, r1, hρ]
  have cfr : ∀ r', r' ≠ O + 13 → (r' < O + 23 ∨ O + 32 ≤ r') → s5.regs r' = s3.regs r' :=
    fun r' a1 a2 => by
      simp (disch := omega) only [hs5, HS.setR_regs, upd_ne]
      rw [r2 _ (by omega)]
  have c17 : s5.regs (O + 17) = q := by rw [cfr _ (by omega) (by omega), b17]
  obtain ⟨v1, v2, v3, -, -, v6⟩ := powW_spec inp B (O + 17) (O + 13) (O + 23) s5 M (by omega)
    (by omega) (by rw [c17]; omega) (by rw [c17, c13]; omega)
  rw [c17, c13] at v1
  rw [c13] at v6
  set s6 := (powW (O + 17) (O + 13) (O + 23)).exec inp s5 with hs6
  have d13 : s6.regs (O + 13) = ρ := by rw [v2 _ (by omega), c13]
  have dn : s6.regs nR = n := by
    rw [v2 _ (by omega), cfr _ (by omega) (by omega), bfr _ (by omega) (by omega) (by omega)]
  have d7 : s6.regs (O + 7) = fv := by
    rw [v2 _ (by omega), cfr _ (by omega) (by omega), bfr _ (by omega) (by omega) (by omega)]
  set s7 := (seqs [cp (O + 14) (O + 23), ar .sub (O + 15) nR (O + 13),
    ar .add (O + 16) (O + 15) (O + 7)]).exec inp s6 with hs7
  have hex : (pR q t nR O).exec inp s = s7 := rfl
  have hco : (pR q t nR O).cost inp B s = kappa B (RAM.bits q) +
      ((powW (O + 17) (O + 11) (O + 23)).cost inp B s1 + (kappa B (RAM.bits (s2.regs (O + 23))) +
      ((rhoW q t nR (O + 11) (O + 12) (O + 23)).cost inp B s3 +
      (kappa B (RAM.bits (s4.regs (O + 23))) + ((powW (O + 17) (O + 13) (O + 23)).cost inp B s5 +
      (seqs [cp (O + 14) (O + 23), ar .sub (O + 15) nR (O + 13),
        ar .add (O + 16) (O + 15) (O + 7)]).cost inp B s6))))) := rfl
  have k7 : (seqs [cp (O + 14) (O + 23), ar .sub (O + 15) nR (O + 13),
      ar .add (O + 16) (O + 15) (O + 7)]).cost inp B s6 ≤ 3 * kappa B (RAM.bits M) := by
    simp (disch := omega) only [cost_seqs_cons, cost_seqs_nil, cost_cp, cost_ar, exec_cp, exec_ar,
      HS.setR_regs, upd_ne, upd_eq, v1, d13, dn, d7, arith_sub]
    have := kappa_bits_le B (a := q ^ ρ) (M := M) (by omega)
    have := kappa_bits_le B (a := n + ρ) (M := M) (by omega)
    have := kappa_bits_le B (a := n - ρ + fv) (M := M) (by omega)
    omega
  have e7 : ∀ r', r' ≠ O + 14 → r' ≠ O + 15 → r' ≠ O + 16 → s7.regs r' = s6.regs r' :=
    fun r' a1 a2 a3 => by
      simp (disch := omega) only [hs7, exec_seqs_cons, exec_seqs_nil, exec_cp, exec_ar,
        HS.setR_regs, upd_ne]
  have e14 : s7.regs (O + 14) = q ^ ρ := by
    simp (disch := omega) only [hs7, exec_seqs_cons, exec_seqs_nil, exec_cp, exec_ar,
      HS.setR_regs, upd_ne, upd_eq, v1]
  have e15 : s7.regs (O + 15) = n - ρ := by
    simp (disch := omega) only [hs7, exec_seqs_cons, exec_seqs_nil, exec_cp, exec_ar,
      HS.setR_regs, upd_ne, upd_eq, d13, dn, arith_sub]
  have e16 : s7.regs (O + 16) = n - ρ + fv := by
    simp (disch := omega) only [hs7, exec_seqs_cons, exec_seqs_nil, exec_cp, exec_ar,
      HS.setR_regs, upd_ne, upd_eq, d13, dn, d7, arith_sub, arith_add]
  have kq := kappa_bits_le B (a := q) (M := M) (by omega)
  have k2 : kappa B (RAM.bits (s2.regs (O + 23))) ≤ kappa B (RAM.bits M) := by
    rw [w1]; exact kappa_bits_le B (by omega)
  have k4 : kappa B (RAM.bits (s4.regs (O + 23))) ≤ kappa B (RAM.bits M) := by
    rw [r1, ← hρ]; exact kappa_bits_le B (by omega)
  have hmem : s7.mem = s.mem := by rw [← hex]; exact exec_mem_of_stores inp _ rfl s
  clear_value s1 s2 s3 s4 s5 s6 s7
  rw [hex]
  refine ⟨?_, ?_, e14, e15, e16, ?_, hmem, ?_, ?_, ?_⟩
  · rw [e7 _ (by omega) (by omega) (by omega), v2 _ (by omega), cfr _ (by omega) (by omega), b12]
  · rw [e7 _ (by omega) (by omega) (by omega), d13]
  · intro r' h
    rw [e7 _ (by omega) (by omega) (by omega), v2 _ (by omega), cfr _ (by omega) (by omega),
      bfr _ (by omega) (by omega) (by omega)]
  · rw [← hex]; exact exec_cur_of_reads inp _ rfl s
  · rw [← hex]; exact exec_out_of_emits inp _ rfl s
  · rw [hco]
    have hv6 : (2 * ρ + 3) * kappa B (RAM.bits M) ≤ (2 * n + 3) * kappa B (RAM.bits M) :=
      Nat.mul_le_mul_right _ (by omega)
    have hy : ((4 * t + 24) * (n + 1) + 2 * hv + 2 * n + 20) * kappa B (RAM.bits M) =
      kappa B (RAM.bits M) + (2 * hv + 3) * kappa B (RAM.bits M) + kappa B (RAM.bits M) +
      ((4 * t + 24) * (n + 1) + 8) * kappa B (RAM.bits M) + kappa B (RAM.bits M) +
      (2 * n + 3) * kappa B (RAM.bits M) + 3 * kappa B (RAM.bits M) := by
      ring
    omega

end PartR

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamParams6
/-!
# Part P (q379): `paramsW`, all fields of `parameters q t n`

`paramsW q t nR PR O` (with `nR, PR < O`, `n = regs nR`, `regs PR` an array id) leaves
`ParamsAt s' O q t n` (layout below), fills the prime table `arr (regs PR) i = primeAt i` for
`i ≤ L`, and writes only registers in `[O, O + 49)`.

Layout: `O+0 r, O+1 K, O+2 b, O+3 Q, O+4 B, O+5 L, O+6 W = b + 1, O+7 f = Nat.log q (L / 2),
O+8 J, O+9 h₁, O+10 h₂, O+11 h, O+12 q^h, O+13 ρ, O+14 q^ρ, O+15 m, O+16 k`,
where `b = ceilLog 2 (r * K + 1)`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ### Size bounds of the outputs -/

section Params
variable (inp : ℕ → ℕ) (B : ℕ)

theorem paramsW_spec_oai (q t nR PR O : ℕ) (s : HS) (M : ℕ) (hq : 2 ≤ q) (hn : nR < O) (hPR : PR < O)
    (hw : ∃ l ≤ s.regs nR, rhoCond q t (parameters q t (s.regs nR)).h l)
    (hM : paramsBound q t (s.regs nR) (s.regs PR) ≤ M) :
    ParamsAt ((paramsW q t nR PR O).exec inp s) O q t (s.regs nR) ∧
    (∀ i ≤ (parameters q t (s.regs nR)).L,
      ((paramsW q t nR PR O).exec inp s).arr (s.regs PR) i = primeAt i) ∧
    (∀ y i, ¬ (y = s.regs PR ∧ i < Nat.count Nat.Prime (primeBound (parameters q t (s.regs nR)).L)) →
      ((paramsW q t nR PR O).exec inp s).arr y i = s.arr y i) ∧
    (∀ r', (r' < O ∨ O + 49 ≤ r') → ((paramsW q t nR PR O).exec inp s).regs r' = s.regs r') ∧
    ((paramsW q t nR PR O).exec inp s).cur = s.cur ∧
    ((paramsW q t nR PR O).exec inp s).out = s.out ∧
    (paramsW q t nR PR O).cost inp B s ≤ paramsCost q t (s.regs nR) * kappa B (RAM.bits M) := by
  unfold paramsBound at hM
  set n := s.regs nR with hnd
  set x := s.regs PR with hx
  set P := parameters q t n with hP
  have hJ : P.J = q ^ Nat.log q (P.L / 2) := rfl
  have hh : P.h = P.h₁ + P.h₂ := rfl
  have hh₁ : P.h₁ = ceilLog q P.L := rfl
  have hh₂ : P.h₂ = ceilLog q (primeAt (P.L - 1)) := rfl
  have hρ : P.ρ = shortLength q t P.h := rfl
  have hm : P.m = n - P.ρ := rfl
  have hk : P.k = P.m + floorLog q P.J := rfl
  have hfl : floorLog q P.J = Nat.log q (P.L / 2) := by
    rw [hJ]; exact Nat.log_pow (by omega) _
  -- part A
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, afr, amem, -, -, ac⟩ := pA_spec inp B q t nR O s M hq hn
    (by rw [← hnd]; omega)
  rw [← hnd, ← hP] at a0 a1 a2 a3 a4 a5 a6 ac
  set s1 := (pA q t nR O).exec inp s with hs1
  -- part F
  obtain ⟨f7, f8, f9, ffr, fmem, -, -, fc⟩ := pF_spec inp B q O s1 M hq (by rw [a5]; omega)
  simp only [a5] at f7 f8 f9 fc
  set s2 := (pF q O).exec inp s1 with hs2
  have e5 : s2.regs (O + 5) = P.L := by rw [ffr _ (by omega), a5]
  have e9 : s2.regs (O + 9) = P.h₁ := by rw [f9, hh₁]
  have e2x : s2.regs PR = x := by rw [ffr _ (by omega), afr _ (by omega)]
  -- part P
  obtain ⟨p10, p11, ptab, parr, pfr, -, -, pc⟩ := pPrime_spec inp B q PR O s2 M hq hPR
    (by rw [e5, e2x, e9]; omega)
  simp only [e5, e9, e2x] at p10 p11 ptab parr pc
  set s3 := (pPrime q PR O).exec inp s2 with hs3
  have e11 : s3.regs (O + 11) = P.h := by rw [p11, hh, hh₂]
  have e7 : s3.regs (O + 7) = Nat.log q (P.L / 2) := by rw [pfr _ (by omega), f7]
  have e3n : s3.regs nR = n := by rw [pfr _ (by omega), ffr _ (by omega), afr _ (by omega)]
  -- part R
  obtain ⟨r12, r13, r14, r15, r16, rfr, rmem, -, -, rc⟩ := pR_spec inp B q t nR O s3 M hq hn
    (by rw [e3n, e11]; exact hw) (by rw [e3n, e11, e7]; omega)
  simp only [e3n, e11, e7] at r12 r13 r14 r15 r16 rc
  set s4 := (pR q t nR O).exec inp s3 with hs4
  have hex : (paramsW q t nR PR O).exec inp s = s4 := rfl
  have hco : (paramsW q t nR PR O).cost inp B s = (pA q t nR O).cost inp B s +
      ((pF q O).cost inp B s1 + ((pPrime q PR O).cost inp B s2 + (pR q t nR O).cost inp B s3)) := rfl
  -- register chains
  have c3 : ∀ r', (r' < O + 10 ∨ (O + 12 ≤ r' ∧ r' < O + 17) ∨ O + 49 ≤ r') → r' < O + 12 →
      s4.regs r' = s2.regs r' := fun r' h1 h2 => by rw [rfr _ (by omega), pfr _ h1]
  clear_value s1 s2 s3 s4
  rw [hex]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [c3 _ (by omega) (by omega), ffr _ (by omega), a0]
  · rw [c3 _ (by omega) (by omega), ffr _ (by omega), a1]
  · rw [c3 _ (by omega) (by omega), ffr _ (by omega), a2]
  · rw [c3 _ (by omega) (by omega), ffr _ (by omega), a3]
  · rw [c3 _ (by omega) (by omega), ffr _ (by omega), a4]
  · rw [c3 _ (by omega) (by omega), ffr _ (by omega), a5]
  · rw [c3 _ (by omega) (by omega), ffr _ (by omega), a6]
  · rw [c3 _ (by omega) (by omega), f7]
  · rw [c3 _ (by omega) (by omega), f8, hJ]
  · rw [c3 _ (by omega) (by omega), f9, hh₁]
  · rw [rfr _ (by omega), p10, hh₂]
  · rw [rfr _ (by omega), e11]
  · exact r12
  · rw [r13, hρ]
  · rw [r14, hρ]
  · rw [r15, hm, hρ]
  · rw [r16, hk, hm, hρ, hfl]
  · intro i hi
    have : s4.arr x i = s3.arr x i := by simp only [HS.arr, rmem]
    rw [this, ptab i hi]
  · intro y i hyi
    have h4 : s4.arr y i = s3.arr y i := by simp only [HS.arr, rmem]
    have h2 : s2.arr y i = s.arr y i := by simp only [HS.arr, fmem, amem]
    rw [h4, parr y i hyi, h2]
  · intro r' h
    rw [rfr _ (by omega), pfr _ (by omega), ffr _ (by omega), afr _ (by omega)]
  · rw [← hex]; exact exec_cur_of_reads inp _ rfl s
  · rw [← hex]; exact exec_out_of_emits inp _ rfl s
  · rw [hco]
    unfold paramsCost
    rw [← hP]
    have hy : ((7 * (P.r * P.K + 1) + 4 * t + 40) + (11 * P.L + 19) +
      ((8 * primeBound P.L + 13) * (primeBound P.L + 1) + 14 * primeBound P.L + 40) +
      ((4 * t + 24) * (n + 1) + 2 * P.h + 2 * n + 20)) * kappa B (RAM.bits M) =
      (7 * (P.r * P.K + 1) + 4 * t + 40) * kappa B (RAM.bits M) +
      (11 * P.L + 19) * kappa B (RAM.bits M) +
      ((8 * primeBound P.L + 13) * (primeBound P.L + 1) + 14 * primeBound P.L + 40) *
        kappa B (RAM.bits M) +
      ((4 * t + 24) * (n + 1) + 2 * P.h + 2 * n + 20) * kappa B (RAM.bits M) := by ring
    omega

end Params

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.paramsW_spec_oai := @EditMulticoloring.Dev.Ram.paramsW_spec_oai
