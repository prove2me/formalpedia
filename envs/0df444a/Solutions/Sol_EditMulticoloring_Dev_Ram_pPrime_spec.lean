-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.pPrime_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:37:05.233039+00:00
-- url     : https://prove2.me/submissions/645710c7-d840-4344-8445-d1d92d837383

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

/-! ### The short length `ρ = shortLength q t h` -/

end Logs

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamParams2
attribute [-simp] _root_.EditMulticoloring.Dev.Ram.arith_xor
/-!
# Part P (q379): the prime table

`primesW PR Mc S`: for every `m < regs Mc` (trial division), store the primes in increasing
order into array `regs PR`: afterwards `arr PR i = Nat.nth Nat.Prime i` for all
`i < Nat.count Nat.Prime (regs Mc)`, and register `S` holds that count.
With `regs Mc > (L + 2) * (2 * (Nat.log 2 (L + 2) + 3))` this covers every `i ≤ L`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ### A Chebyshev bound on the `N`-th prime (copied from the q373 record,
`Solutions/EditMulticoloring/EncoderRedundancyAux1.lean`, `nth_prime_le`). -/

theorem ramP_two_mul_add_one_le_two_pow : ∀ s : ℕ, 3 ≤ s → 2 * s + 1 ≤ 2 ^ s
  | 0, h => by omega
  | 1, h => by omega
  | 2, h => by omega
  | 3, _ => by norm_num
  | s + 4, _ => by
    have := ramP_two_mul_add_one_le_two_pow (s + 3) (by omega)
    rw [pow_succ]; omega

/-- A Chebyshev-type upper bound on the `N`-th prime (zero based). -/
theorem ramP_nth_prime_le (N : ℕ) :
    Nat.nth Nat.Prime N ≤ (N + 2) * (2 * (Nat.log 2 (N + 2) + 3)) := by
  set s := Nat.log 2 (N + 2) + 3 with hs
  set x := (N + 2) * (2 * s) with hx
  have h1 : N + 2 < 2 ^ s := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (N + 2)
    calc N + 2 < 2 ^ (Nat.log 2 (N + 2) + 1) := this
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 := ramP_two_mul_add_one_le_two_pow s (by omega)
  have h3 : x + 1 ≤ 2 ^ (2 * s) := by
    have : (N + 2) * (2 * s + 1) ≤ 2 ^ s * 2 ^ s := Nat.mul_le_mul h1.le h2
    rw [two_mul s, pow_add]
    have : (N + 2) * (2 * s + 1) = x + (N + 2) := by rw [hx]; ring
    omega
  have hx12 : 12 ≤ x := by
    have : 6 ≤ 2 * s := by omega
    calc 12 = 2 * 6 := by norm_num
      _ ≤ (N + 2) * (2 * s) := Nat.mul_le_mul (by omega) this
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlx : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hlx1 : Real.log (x : ℝ) ≤ Real.log ((x : ℝ) + 1) :=
    Real.log_le_log (by positivity) (by linarith)
  have h4 : Real.log ((x : ℝ) + 1) ≤ (2 * s : ℕ) * Real.log 2 := by
    rw [← Real.log_pow]
    apply Real.log_le_log (by positivity)
    exact_mod_cast h3
  have h5 : ((N : ℝ) + 1) ≤ ((x : ℝ) * Real.log 2 - Real.log ((x : ℝ) + 1)) / Real.log x := by
    rw [le_div_iff₀ hlx]
    have hxr : (x : ℝ) = ((N : ℝ) + 2) * ((2 * s : ℕ) : ℝ) := by rw [hx]; push_cast; ring
    have : ((N : ℝ) + 2) * Real.log ((x : ℝ) + 1) ≤ (x : ℝ) * Real.log 2 := by
      calc ((N : ℝ) + 2) * Real.log ((x : ℝ) + 1)
          ≤ ((N : ℝ) + 2) * (((2 * s : ℕ) : ℝ) * Real.log 2) :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = (x : ℝ) * Real.log 2 := by rw [hxr]; ring
    nlinarith
  have h6 := Chebyshev.pi_ge x
  have h7 : N < Nat.primeCounting x := by
    have : (N : ℝ) < (Nat.primeCounting x : ℝ) := by linarith
    exact_mod_cast this
  have h8 : Nat.nth Nat.Prime N < x + 1 := by
    apply Nat.nth_lt_of_lt_count
    rw [← Nat.primeCounting', ← Nat.primeCounting_eq_primeCounting'_succ] at *
    exact h7
  omega

/-- Indices below the count of primes below `M`. -/
theorem lt_count_prime_of_nth_lt {i M : ℕ} (h : Nat.nth Nat.Prime i < M) :
    i < Nat.count Nat.Prime M := by
  have h1 : Nat.count Nat.Prime (Nat.nth Nat.Prime i + 1) = i + 1 := by
    rw [Nat.count_succ, Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime,
      if_pos (Nat.prime_nth_prime i)]
  have h2 := Nat.count_monotone Nat.Prime (show Nat.nth Nat.Prime i + 1 ≤ M by omega)
  omega

theorem lt_count_prime_of_le {i L M : ℕ} (hi : i ≤ L)
    (hM : (L + 2) * (2 * (Nat.log 2 (L + 2) + 3)) < M) : i < Nat.count Nat.Prime M := by
  apply lt_count_prime_of_nth_lt
  have h1 : Nat.nth Nat.Prime i ≤ Nat.nth Nat.Prime L :=
    Nat.nth_monotone Nat.infinite_setOfPred_prime hi
  have := ramP_nth_prime_le L
  omega

/-- Trial division characterisation of primality. -/
theorem prime_iff_trial (m : ℕ) : Nat.Prime m ↔ 1 < m ∧ ∀ d < m, 1 < d → m % d ≠ 0 := by
  rw [Nat.prime_def_lt']
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by omega, fun d hd h1d h0 => h2 d (by omega) hd (Nat.dvd_of_mod_eq_zero h0)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨by omega, fun d h2d hd hdv => h2 d hd (by omega) (Nat.mod_eq_zero_of_dvd hdv)⟩

section Primes
variable (inp : ℕ → ℕ) (B : ℕ)

theorem primeTest_frame (S : ℕ) (s : HS) (r' : ℕ) (h : r' < S + 3 ∨ S + 9 ≤ r') :
    ((primeTest S).exec inp s).regs r' = s.regs r' := by
  apply exec_regs_of_not_mem
  simp only [primeTest, ptBody, forLoop, seqs, Cmd.wregs, lit, ar, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, and_true, true_and]
  omega

theorem primeTest_spec (S : ℕ) (s : HS) (M : ℕ) (hM : 2 * s.regs (S + 2) + 1 ≤ M) :
    ((primeTest S).exec inp s).regs (S + 3) = (if Nat.Prime (s.regs (S + 2)) then 1 else 0) ∧
    (∀ r', (r' < S + 3 ∨ S + 9 ≤ r') → ((primeTest S).exec inp s).regs r' = s.regs r') ∧
    ((primeTest S).exec inp s).mem = s.mem ∧
    ((primeTest S).exec inp s).cur = s.cur ∧
    ((primeTest S).exec inp s).out = s.out ∧
    (primeTest S).cost inp B s ≤ (8 * s.regs (S + 2) + 5) * kappa B (RAM.bits M) := by
  set m := s.regs (S + 2) with hm
  set s1 := (seqs [lit (S + 4) 1, ar .lt (S + 3) (S + 4) (S + 2)]).exec inp s with hs1
  have e2 : s1.regs (S + 2) = m := by simp (disch := omega) [hs1, upd_ne, hm]
  have K := forLoop_spec inp B (S + 5) (S + 2) (S + 6) (ptBody S) s1 (by omega) (by omega)
    (fun k st => st.regs (S + 3) = (if 1 < m ∧ ∀ d < k, 1 < d → m % d ≠ 0 then 1 else 0) ∧
      st.regs (S + 4) = 1 ∧ st.regs (S + 2) = m)
    (fun _ => 5 * kappa B (RAM.bits M))
    ⟨by simp (disch := omega) [hs1, upd_ne, upd_eq, hm],
     by simp (disch := omega) [hs1, upd_ne], by simp (disch := omega) [hs1, upd_ne, hm]⟩
    (by
      intro k hk st ⟨hf, h1, h2⟩ hi
      rw [e2] at hk
      have ek : ((ptBody S).exec inp st).regs (S + 5) = k := by
        rw [exec_regs_of_not_mem]; exact hi
        simp only [ptBody, seqs, Cmd.wregs, lit, ar, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false, not_or, not_false_eq_true, and_true, true_and]; omega
      have e1 := kappa_bits_le B (a := 1 + k) (M := M) (by omega)
      have e3 := kappa_bits_le B (a := m + k) (M := M) (by omega)
      have e4 := kappa_bits_le B (a := m % k) (M := M) (by have := Nat.mod_le m k; omega)
      have e5 := kappa_bits_le B (a := 0) (M := M) (by omega)
      have e6 := kappa_bits_le B (a := 1) (M := M) (by omega)
      by_cases hk1 : 1 < k
      · by_cases hmk : m % k = 0
        · refine ⟨ek, ⟨?_, ?_, ?_⟩, ?_⟩
          · simp (disch := omega) only [ptBody, exec_seqs_cons, exec_seqs_nil, exec_ar, exec_ifz,
              exec_lit, exec_skip, HS.setR_regs, upd_ne, upd_eq, h1, hi, h2, arith_lt, arith_mod,
              hk1, hmk, if_true, if_false, one_ne_zero]
            rw [if_neg]
            rintro ⟨-, hall⟩
            exact hall k (by omega) hk1 hmk
          · simp (disch := omega) [ptBody, upd_ne, upd_eq, h1, hi, h2, hk1, hmk]
          · simp (disch := omega) [ptBody, upd_ne, upd_eq, h1, hi, h2, hk1, hmk]
          · simp (disch := omega) only [ptBody, cost_seqs_cons, cost_seqs_nil, cost_ar, cost_ifz,
              cost_lit, cost_skip, exec_seqs_cons, exec_ar, HS.setR_regs, upd_ne, upd_eq, h1, hi,
              h2, arith_lt, arith_mod, hk1, hmk, if_true, one_ne_zero, if_false]
            omega
        · refine ⟨ek, ⟨?_, ?_, ?_⟩, ?_⟩
          · simp (disch := omega) only [ptBody, exec_seqs_cons, exec_seqs_nil, exec_ar, exec_ifz,
              exec_lit, exec_skip, HS.setR_regs, upd_ne, upd_eq, h1, hi, h2, arith_lt, arith_mod,
              hk1, hmk, if_true, if_false, one_ne_zero, hf]
            congr 1
            apply propext
            constructor
            · rintro ⟨a, b⟩; refine ⟨a, fun d hd h1d => ?_⟩
              rcases Nat.lt_succ_iff_lt_or_eq.mp hd with hd | hd
              · exact b d hd h1d
              · rw [hd]; exact hmk
            · rintro ⟨a, b⟩; exact ⟨a, fun d hd h1d => b d (by omega) h1d⟩
          · simp (disch := omega) [ptBody, upd_ne, upd_eq, h1, hi, h2, hk1, hmk]
          · simp (disch := omega) [ptBody, upd_ne, upd_eq, h1, hi, h2, hk1, hmk]
          · simp (disch := omega) only [ptBody, cost_seqs_cons, cost_seqs_nil, cost_ar, cost_ifz,
              cost_lit, cost_skip, exec_seqs_cons, exec_ar, HS.setR_regs, upd_ne, upd_eq, h1, hi,
              h2, arith_lt, arith_mod, hk1, hmk, if_true, one_ne_zero, if_false]
            omega
      · refine ⟨ek, ⟨?_, ?_, ?_⟩, ?_⟩
        · simp (disch := omega) only [ptBody, exec_seqs_cons, exec_seqs_nil, exec_ar, exec_ifz,
            exec_lit, exec_skip, HS.setR_regs, upd_ne, upd_eq, h1, hi, h2, arith_lt, arith_mod,
            hk1, if_true, if_false, one_ne_zero, hf]
          congr 1
          apply propext
          constructor
          · rintro ⟨a, b⟩; refine ⟨a, fun d hd h1d => ?_⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hd with hd | hd
            · exact b d hd h1d
            · omega
          · rintro ⟨a, b⟩; exact ⟨a, fun d hd h1d => b d (by omega) h1d⟩
        · simp (disch := omega) [ptBody, upd_ne, upd_eq, h1, hi, h2, hk1]
        · simp (disch := omega) [ptBody, upd_ne, upd_eq, h1, hi, h2, hk1]
        · simp (disch := omega) only [ptBody, cost_seqs_cons, cost_seqs_nil, cost_ar, cost_ifz,
            cost_lit, cost_skip, exec_seqs_cons, exec_ar, HS.setR_regs, upd_ne, upd_eq, h1, hi,
            h2, arith_lt, arith_mod, hk1, if_true, one_ne_zero, if_false]
          omega)
  obtain ⟨⟨k1, -, -⟩, k4⟩ := K
  rw [e2] at k1 k4
  have hex : (primeTest S).exec inp s = (forLoop (S + 5) (S + 2) (S + 6) (ptBody S)).exec inp s1 := rfl
  have hco : (primeTest S).cost inp B s = (seqs [lit (S + 4) 1, ar .lt (S + 3) (S + 4) (S + 2)]).cost
      inp B s + (forLoop (S + 5) (S + 2) (S + 6) (ptBody S)).cost inp B s1 := rfl
  refine ⟨?_, primeTest_frame inp S s, exec_mem_of_stores inp _ rfl s,
    exec_cur_of_reads inp _ rfl s, exec_out_of_emits inp _ rfl s, ?_⟩
  · rw [hex, k1]
    congr 1
    exact propext (prime_iff_trial m).symm
  · rw [hco]
    simp (disch := omega) only [cost_seqs_cons, cost_seqs_nil, cost_lit, cost_ar, exec_seqs_cons,
      exec_lit, HS.setR_regs, upd_ne, upd_eq, ← hm]
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at k4
    have e1 := kappa_bits_le B (a := 1) (M := M) (by omega)
    have e3 := kappa_bits_le B (a := 1 + m) (M := M) (by omega)
    have e4 := kappa_bits_le B (a := m) (M := M) (by omega)
    have hz : 3 * (m + 1) * kappa B (RAM.bits m) ≤ 3 * (m + 1) * kappa B (RAM.bits M) :=
      Nat.mul_le_mul_left _ e4
    have hy : (8 * m + 5) * kappa B (RAM.bits M) =
      3 * (m + 1) * kappa B (RAM.bits M) + m * (5 * kappa B (RAM.bits M)) +
        2 * kappa B (RAM.bits M) := by ring
    omega

theorem primesW_frame (PR Mc S : ℕ) (s : HS) (r' : ℕ) (h : r' < S ∨ S + 10 ≤ r') :
    ((primesW PR Mc S).exec inp s).regs r' = s.regs r' := by
  apply exec_regs_of_not_mem
  simp only [primesW, primesBody, primeTest, ptBody, forLoop, seqs, Cmd.wregs, lit, ar, ast,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true,
    and_true, true_and]
  omega

theorem primesW_spec (PR Mc S : ℕ) (s : HS) (M : ℕ) (hPR : PR < S) (hMc : Mc < S)
    (hM : s.regs PR + 2 * s.regs Mc + 2 ≤ M) :
    ((primesW PR Mc S).exec inp s).regs S = Nat.count Nat.Prime (s.regs Mc) ∧
    (∀ i < Nat.count Nat.Prime (s.regs Mc),
      ((primesW PR Mc S).exec inp s).arr (s.regs PR) i = Nat.nth Nat.Prime i) ∧
    (∀ y i, ¬ (y = s.regs PR ∧ i < Nat.count Nat.Prime (s.regs Mc)) →
      ((primesW PR Mc S).exec inp s).arr y i = s.arr y i) ∧
    (∀ r', (r' < S ∨ S + 10 ≤ r') → ((primesW PR Mc S).exec inp s).regs r' = s.regs r') ∧
    ((primesW PR Mc S).exec inp s).cur = s.cur ∧
    ((primesW PR Mc S).exec inp s).out = s.out ∧
    (primesW PR Mc S).cost inp B s ≤
      (8 * s.regs Mc + 13) * (s.regs Mc + 1) * kappa B (RAM.bits M) := by
  set x := s.regs PR with hx
  set N := s.regs Mc with hN
  set s1 := s.setR S 0 with hs1
  have hN1 : s1.regs Mc = N := by simp (disch := omega) [hs1, upd_ne, hN]
  have K := forLoop_spec inp B (S + 2) Mc (S + 1) (primesBody PR S) s1 (by omega) (by omega)
    (fun k st => st.regs S = Nat.count Nat.Prime k ∧
      (∀ i < Nat.count Nat.Prime k, st.arr x i = Nat.nth Nat.Prime i) ∧
      (∀ y i, ¬ (y = x ∧ i < Nat.count Nat.Prime k) → st.arr y i = s.arr y i) ∧
      (∀ r', (r' < S ∨ S + 10 ≤ r') → st.regs r' = s.regs r'))
    (fun _ => (8 * N + 9) * kappa B (RAM.bits M))
    ⟨by simp [hs1], fun i hi => by simp at hi, fun y i _ => rfl,
      fun r' h => by simp (disch := omega) [hs1, upd_ne]⟩
    (by
      intro k hk st ⟨hc, htab, hfr, hr⟩ hi
      rw [hN1] at hk
      have ex : st.regs PR = x := hr PR (Or.inl hPR)
      have hck : Nat.count Nat.Prime k ≤ k := Nat.count_le Nat.Prime
      obtain ⟨p1, p2, p3, -, -, p6⟩ := primeTest_spec inp B S st M (by rw [hi]; omega)
      rw [hi] at p1 p6
      set s2 := (primeTest S).exec inp st with hs2
      have f0 : s2.regs S = Nat.count Nat.Prime k := by rw [p2 _ (by omega), hc]
      have f2 : s2.regs (S + 2) = k := by rw [p2 _ (by omega), hi]
      have fx : s2.regs PR = x := by rw [p2 _ (by omega), ex]
      have farr : ∀ y i, s2.arr y i = st.arr y i := fun y i => by simp [HS.arr, p3]
      have hex : (primesBody PR S).exec inp st = (Cmd.ifz (S + 3) .skip (seqs [ast PR S (S + 2),
          lit (S + 9) 1, ar .add S S (S + 9)])).exec inp s2 := rfl
      have hco : (primesBody PR S).cost inp B st = (primeTest S).cost inp B st +
          (Cmd.ifz (S + 3) .skip (seqs [ast PR S (S + 2),
          lit (S + 9) 1, ar .add S S (S + 9)])).cost inp B s2 := rfl
      have e1 := kappa_bits_le B (a := 1) (M := M) (by omega)
      have e0 := kappa_bits_le B (a := 0) (M := M) (by omega)
      have e2 := kappa_bits_le B (a := x + Nat.count Nat.Prime k + k) (M := M) (by omega)
      have e3 := kappa_bits_le B (a := Nat.count Nat.Prime k + 1) (M := M) (by omega)
      have hp6 : (8 * k + 5) * kappa B (RAM.bits M) ≤ (8 * N + 5) * kappa B (RAM.bits M) :=
        Nat.mul_le_mul_right _ (by omega)
      have hy : (8 * N + 9) * kappa B (RAM.bits M) =
        (8 * N + 5) * kappa B (RAM.bits M) + 4 * kappa B (RAM.bits M) := by ring
      by_cases hp : Nat.Prime k
      · have hcs : Nat.count Nat.Prime (k + 1) = Nat.count Nat.Prime k + 1 := by
          rw [Nat.count_succ, if_pos hp]
        rw [if_pos hp] at p1
        refine ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
        · rw [hex]; simp (disch := omega) [p1, upd_ne, f2]
        · rw [hex]; simp (disch := omega) [p1, upd_ne, upd_eq, f0, hcs]
        · intro i hi'
          rw [hex]; simp (disch := omega) only [exec_ifz, p1, one_ne_zero, if_false, exec_seqs_cons,
            exec_seqs_nil, exec_ast, exec_lit, exec_ar, HS.setR_arr, HS.store_arr, HS.setR_regs,
            upd_ne, upd_eq, fx, f0, f2]
          rw [hcs] at hi'
          by_cases hie : i = Nat.count Nat.Prime k
          · rw [if_pos (by simp [hie]), hie]; exact (Nat.nth_count hp).symm
          · rw [if_neg (by simp [hie]), farr]; exact htab i (by omega)
        · intro y i hyi
          rw [hex]; simp (disch := omega) only [exec_ifz, p1, one_ne_zero, if_false, exec_seqs_cons,
            exec_seqs_nil, exec_ast, exec_lit, exec_ar, HS.setR_arr, HS.store_arr, HS.setR_regs,
            upd_ne, upd_eq, fx, f0, f2]
          rw [hcs] at hyi
          rw [if_neg (by rintro ⟨h1, h2⟩; exact hyi ⟨h1, by omega⟩), farr]
          exact hfr y i (by rintro ⟨h1, h2⟩; exact hyi ⟨h1, by omega⟩)
        · intro r' h'
          rw [hex]; simp (disch := omega) only [exec_ifz, p1, one_ne_zero, if_false, exec_seqs_cons,
            exec_seqs_nil, exec_ast, exec_lit, exec_ar, HS.setR_regs, HS.store_regs, upd_ne,
            HS.setR_regs]
          rw [p2 r' (by omega)]; exact hr r' h'
        · rw [hco]
          simp (disch := omega) only [cost_ifz, p1, one_ne_zero, if_false, cost_seqs_cons,
            cost_seqs_nil, cost_ast, cost_lit, cost_ar, exec_ast, exec_lit, HS.store_regs,
            HS.setR_regs, upd_ne, upd_eq, fx, f0, f2]
          omega
      · have hcs : Nat.count Nat.Prime (k + 1) = Nat.count Nat.Prime k := by
          rw [Nat.count_succ, if_neg hp]; rfl
        rw [if_neg hp] at p1
        refine ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
        · rw [hex]; simp (disch := omega) [p1, upd_ne, f2]
        · rw [hex]; simp (disch := omega) [p1, upd_ne, upd_eq, f0, hcs]
        · intro i hi'
          rw [hex]; simp only [exec_ifz, p1, if_true, exec_skip, HS.setR_arr, farr]
          rw [hcs] at hi'; exact htab i hi'
        · intro y i hyi
          rw [hex]; simp only [exec_ifz, p1, if_true, exec_skip, HS.setR_arr, farr]
          rw [hcs] at hyi; exact hfr y i hyi
        · intro r' h'
          rw [hex]; simp (disch := omega) only [exec_ifz, p1, if_true, exec_skip, HS.setR_regs, upd_ne]
          rw [p2 r' (by omega)]; exact hr r' h'
        · rw [hco]
          simp (disch := omega) only [cost_ifz, p1, if_true, cost_skip]
          omega)
  obtain ⟨⟨k1, k2, k3, -⟩, k4⟩ := K
  simp only [hN1] at k1 k2 k3 k4
  have hex : (primesW PR Mc S).exec inp s = (forLoop (S + 2) Mc (S + 1) (primesBody PR S)).exec inp s1 := rfl
  have hco : (primesW PR Mc S).cost inp B s = kappa B (RAM.bits 0) +
      (forLoop (S + 2) Mc (S + 1) (primesBody PR S)).cost inp B s1 := rfl
  refine ⟨by rw [hex]; exact k1, by rw [hex]; exact k2, by rw [hex]; exact k3,
    primesW_frame inp PR Mc S s, exec_cur_of_reads inp _ rfl s, exec_out_of_emits inp _ rfl s, ?_⟩
  rw [hco]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at k4
  have e0 := kappa_bits_le B (a := 0) (M := M) (by omega)
  have e4 := kappa_bits_le B (a := N) (M := M) (by omega)
  have hz : 3 * (N + 1) * kappa B (RAM.bits N) ≤ 3 * (N + 1) * kappa B (RAM.bits M) :=
    Nat.mul_le_mul_left _ e4
  have hpoly : 3 * (N + 1) + N * (8 * N + 9) + 1 ≤ (8 * N + 13) * (N + 1) := by nlinarith
  have hy := Nat.mul_le_mul_right (kappa B (RAM.bits M)) hpoly
  have hy2 : (3 * (N + 1) + N * (8 * N + 9) + 1) * kappa B (RAM.bits M) =
    3 * (N + 1) * kappa B (RAM.bits M) + N * ((8 * N + 9) * kappa B (RAM.bits M)) +
      kappa B (RAM.bits M) := by ring
  omega

end Primes

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

theorem primeAt_lt_primeBound {i L : ℕ} (hi : i ≤ L) : primeAt i < primeBound L := by
  have := lt_count_prime_of_le (M := primeBound L) hi (by unfold primeBound; omega)
  exact Nat.nth_lt_of_lt_count this

theorem le_primeBound (L : ℕ) : 6 * (L + 2) + 1 ≤ primeBound L := by
  unfold primeBound
  have : 6 ≤ 2 * (Nat.log 2 (L + 2) + 3) := by omega
  nlinarith

section PartP
variable (inp : ℕ → ℕ) (B : ℕ)

theorem pPrime_spec_oai (q PR O : ℕ) (s : HS) (M : ℕ) (hq : 2 ≤ q) (hPR : PR < O)
    (hM : (primeBound (s.regs (O + 5)) + 2) * (q + 1) + s.regs PR +
      3 * primeBound (s.regs (O + 5)) + s.regs (O + 9) + 10 ≤ M) :
    ((pPrime q PR O).exec inp s).regs (O + 10) = ceilLog q (primeAt (s.regs (O + 5) - 1)) ∧
    ((pPrime q PR O).exec inp s).regs (O + 11) =
      s.regs (O + 9) + ceilLog q (primeAt (s.regs (O + 5) - 1)) ∧
    (∀ i ≤ s.regs (O + 5), ((pPrime q PR O).exec inp s).arr (s.regs PR) i = primeAt i) ∧
    (∀ y i, ¬ (y = s.regs PR ∧ i < Nat.count Nat.Prime (primeBound (s.regs (O + 5)))) →
      ((pPrime q PR O).exec inp s).arr y i = s.arr y i) ∧
    (∀ r', (r' < O + 10 ∨ (O + 12 ≤ r' ∧ r' < O + 17) ∨ O + 49 ≤ r') →
      ((pPrime q PR O).exec inp s).regs r' = s.regs r') ∧
    ((pPrime q PR O).exec inp s).cur = s.cur ∧
    ((pPrime q PR O).exec inp s).out = s.out ∧
    (pPrime q PR O).cost inp B s ≤
      ((8 * primeBound (s.regs (O + 5)) + 13) * (primeBound (s.regs (O + 5)) + 1) +
        14 * primeBound (s.regs (O + 5)) + 40) * kappa B (RAM.bits M) := by
  set L := s.regs (O + 5) with hLd
  set Mc := primeBound L with hMc
  set x := s.regs PR with hx
  set h1 := s.regs (O + 9) with hh1
  set lg := Nat.log 2 (L + 2) with hlg
  set pa := primeAt (L - 1) with hpa
  have hMc' : Mc = (L + 2) * ((lg + 3) + (lg + 3)) + 1 := by rw [hMc, primeBound]; ring
  have hpaM : pa < Mc := primeAt_lt_primeBound (by omega)
  have h6 := le_primeBound L
  rw [← hMc] at h6
  have hlgL : lg ≤ L + 2 := log_le_of_pos (le_refl 2)
  have hMq : Mc + 2 ≤ (Mc + 2) * (q + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hqq : q + 1 ≤ (Mc + 2) * (q + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have hpq : (pa + 2) * (q + 1) ≤ (Mc + 2) * (q + 1) := Nat.mul_le_mul_right _ (by omega)
  have hmul : L + 2 + (lg + 3 + (lg + 3)) ≤ Mc := by
    rw [hMc']; nlinarith
  clear_value Mc lg pa
  -- block 1
  set s1 := (seqs [lit (O + 17) 2, lit (O + 19) 2, ar .add (O + 18) (O + 5) (O + 19)]).exec inp s
    with hs1
  have a17 : s1.regs (O + 17) = 2 := by
    simp (disch := omega) only [hs1, exec_seqs_cons, exec_seqs_nil, exec_lit, exec_ar, HS.setR_regs,
      upd_ne, upd_eq]
  have a18 : s1.regs (O + 18) = L + 2 := by
    simp (disch := omega) only [hs1, exec_seqs_cons, exec_seqs_nil, exec_lit, exec_ar, HS.setR_regs,
      upd_ne, upd_eq, arith_add, hLd]
  have afr : ∀ r', r' ≠ O + 17 → r' ≠ O + 18 → r' ≠ O + 19 → s1.regs r' = s.regs r' :=
    fun r' a1 a2 a3 => by
      simp (disch := omega) only [hs1, exec_seqs_cons, exec_seqs_nil, exec_lit, exec_ar,
        HS.setR_regs, upd_ne]
  have k1 : (seqs [lit (O + 17) 2, lit (O + 19) 2, ar .add (O + 18) (O + 5) (O + 19)]).cost inp B s ≤
      3 * kappa B (RAM.bits M) := by
    simp (disch := omega) only [cost_seqs_cons, cost_seqs_nil, cost_lit, cost_ar, exec_lit,
      HS.setR_regs, upd_ne, upd_eq, ← hLd]
    have := kappa_bits_le B (a := 2) (M := M) (by omega)
    have := kappa_bits_le B (a := L + 2) (M := M) (by omega)
    omega
  -- floorLog
  obtain ⟨f1, -, f3, -, -, -, f7⟩ := floorLogW_spec inp B (O + 17) (O + 18) (O + 18) (O + 23) s1 M
    (by omega) (by omega) (by omega) (by rw [a17]) (by rw [a17, a18]; exact log_le_of_pos (le_refl 2))
    (by rw [a17, a18]; omega)
  rw [a17, a18, ← hlg] at f1
  rw [a18] at f7
  set s2 := (floorLogW (O + 17) (O + 18) (O + 18) (O + 23)).exec inp s1 with hs2
  have e18 : s2.regs (O + 18) = L + 2 := by rw [f3 _ (by omega), a18]
  -- block 2
  set s3 := (seqs [lit (O + 19) 3, ar .add (O + 19) (O + 23) (O + 19),
    ar .add (O + 19) (O + 19) (O + 19), ar .mul (O + 18) (O + 18) (O + 19), lit (O + 19) 1,
    ar .add (O + 18) (O + 18) (O + 19)]).exec inp s2 with hs3
  have b18 : s3.regs (O + 18) = Mc := by
    simp (disch := omega) only [hs3, exec_seqs_cons, exec_seqs_nil, exec_lit, exec_ar, HS.setR_regs,
      upd_ne, upd_eq, arith_add, arith_mul, e18, f1]
    rw [hMc']
  have bfr : ∀ r', r' ≠ O + 18 → r' ≠ O + 19 → s3.regs r' = s2.regs r' := fun r' a1 a2 => by
    simp (disch := omega) only [hs3, exec_seqs_cons, exec_seqs_nil, exec_lit, exec_ar,
      HS.setR_regs, upd_ne]
  have k3 : (seqs [lit (O + 19) 3, ar .add (O + 19) (O + 23) (O + 19),
      ar .add (O + 19) (O + 19) (O + 19), ar .mul (O + 18) (O + 18) (O + 19), lit (O + 19) 1,
      ar .add (O + 18) (O + 18) (O + 19)]).cost inp B s2 ≤ 6 * kappa B (RAM.bits M) := by
    simp (disch := omega) only [cost_seqs_cons, cost_seqs_nil, cost_lit, cost_ar, exec_lit, exec_ar,
      HS.setR_regs, upd_ne, upd_eq, arith_add, arith_mul, e18, f1]
    have := kappa_bits_le B (a := 3) (M := M) (by omega)
    have := kappa_bits_le B (a := lg + 3) (M := M) (by omega)
    have := kappa_bits_le B (a := lg + 3 + (lg + 3)) (M := M) (by omega)
    have := kappa_bits_le B (a := L + 2 + (lg + 3 + (lg + 3))) (M := M) (by omega)
    have := kappa_bits_le B (a := 1) (M := M) (by omega)
    have := kappa_bits_le B (a := (L + 2) * (lg + 3 + (lg + 3)) + 1) (M := M) (by omega)
    omega
  -- primes
  have b5 : s3.regs (O + 5) = L := by
    rw [bfr _ (by omega) (by omega), f3 _ (by omega), afr _ (by omega) (by omega) (by omega)]
  have bx : s3.regs PR = x := by
    rw [bfr _ (by omega) (by omega), f3 _ (by omega), afr _ (by omega) (by omega) (by omega)]
  obtain ⟨p1, p2, p3, p4, -, -, p7⟩ := primesW_spec inp B PR (O + 18) (O + 23) s3 M (by omega) (by omega)
    (by rw [bx, b18]; omega)
  rw [b18, bx] at p2 p3
  rw [b18] at p7
  set s4 := (primesW PR (O + 18) (O + 23)).exec inp s3 with hs4
  have hcnt : L - 1 < Nat.count Nat.Prime Mc := by
    rw [hMc]; exact lt_count_prime_of_le (L := L) (by omega) (by unfold primeBound; omega)
  have c5 : s4.regs (O + 5) = L := by rw [p4 _ (by omega), b5]
  have cx : s4.regs PR = x := by rw [p4 _ (by omega), bx]
  -- block 3
  set s5 := (seqs [lit (O + 19) 1, ar .sub (O + 18) (O + 5) (O + 19), ald (O + 18) PR (O + 18),
     lit (O + 17) q]).exec inp s4 with hs5
  have hpa4 : s4.arr x (L - 1) = pa := by rw [p2 _ hcnt, hpa]; rfl
  have d18 : s5.regs (O + 18) = pa := by
    simp (disch := omega) only [hs5, exec_seqs_cons, exec_seqs_nil, exec_lit, exec_ar, exec_ald,
      HS.setR_regs, HS.setR_arr, upd_ne, upd_eq, arith_sub, c5, cx, hpa4]
  have d17 : s5.regs (O + 17) = q := by
    simp (disch := omega) only [hs5, exec_seqs_cons, exec_seqs_nil, exec_lit, exec_ar, exec_ald,
      HS.setR_regs, upd_ne, upd_eq]
  have dfr : ∀ r', r' ≠ O + 17 → r' ≠ O + 18 → r' ≠ O + 19 → s5.regs r' = s4.regs r' :=
    fun r' a1 a2 a3 => by
      simp (disch := omega) only [hs5, exec_seqs_cons, exec_seqs_nil, exec_lit, exec_ar, exec_ald,
        HS.setR_regs, upd_ne]
  have dmem : s5.mem = s4.mem := by
    simp only [hs5, exec_seqs_cons, exec_seqs_nil, exec_lit, exec_ar, exec_ald, HS.setR_mem]
  have k5 : (seqs [lit (O + 19) 1, ar .sub (O + 18) (O + 5) (O + 19), ald (O + 18) PR (O + 18),
     lit (O + 17) q]).cost inp B s4 ≤ 4 * kappa B (RAM.bits M) := by
    simp (disch := omega) only [cost_seqs_cons, cost_seqs_nil, cost_lit, cost_ar, cost_ald, exec_lit,
      exec_ar, HS.setR_regs, HS.setR_arr, upd_ne, upd_eq, arith_sub, c5, cx, hpa4]
    have := kappa_bits_le B (a := 1) (M := M) (by omega)
    have := kappa_bits_le B (a := L + 1) (M := M) (by omega)
    have := kappa_bits_le B (a := x + (L - 1) + pa) (M := M) (by omega)
    have := kappa_bits_le B (a := q) (M := M) (by omega)
    omega
  -- ceilLog
  obtain ⟨g1, -, g3, -, -, -, g7⟩ := ceilLogW_spec inp B (O + 17) (O + 18) (O + 18) (O + 23) s5 M
    (by omega) (by omega) (by omega) (by rw [d17]; exact hq)
    (by rw [d17, d18]; exact log_le_of_pos hq) (by rw [d17, d18]; omega)
  rw [d17, d18] at g1
  rw [d18] at g7
  set s6 := (ceilLogW (O + 17) (O + 18) (O + 18) (O + 23)).exec inp s5 with hs6
  have hcl := ceilLog_le_succ q pa hq
  have g9 : s6.regs (O + 9) = h1 := by
    rw [g3 _ (by omega), dfr _ (by omega) (by omega) (by omega), p4 _ (by omega),
      bfr _ (by omega) (by omega), f3 _ (by omega), afr _ (by omega) (by omega) (by omega)]
  have g6mem : s6.mem = s4.mem := by
    rw [hs6, exec_mem_of_stores inp _ rfl s5, dmem]
  set s7 := (seqs [cp (O + 10) (O + 23), ar .add (O + 11) (O + 9) (O + 10)]).exec inp s6 with hs7
  have k7 : (seqs [cp (O + 10) (O + 23), ar .add (O + 11) (O + 9) (O + 10)]).cost inp B s6 ≤
      2 * kappa B (RAM.bits M) := by
    simp (disch := omega) only [cost_seqs_cons, cost_seqs_nil, cost_cp, cost_ar, exec_cp,
      HS.setR_regs, upd_ne, upd_eq, g1, g9]
    have := kappa_bits_le B (a := ceilLog q pa) (M := M) (by omega)
    have := kappa_bits_le B (a := h1 + ceilLog q pa) (M := M) (by omega)
    omega
  have hex : (pPrime q PR O).exec inp s = s7 := rfl
  have hco : (pPrime q PR O).cost inp B s =
      (seqs [lit (O + 17) 2, lit (O + 19) 2, ar .add (O + 18) (O + 5) (O + 19)]).cost inp B s +
      ((floorLogW (O + 17) (O + 18) (O + 18) (O + 23)).cost inp B s1 +
      ((seqs [lit (O + 19) 3, ar .add (O + 19) (O + 23) (O + 19),
        ar .add (O + 19) (O + 19) (O + 19), ar .mul (O + 18) (O + 18) (O + 19), lit (O + 19) 1,
        ar .add (O + 18) (O + 18) (O + 19)]).cost inp B s2 +
      ((primesW PR (O + 18) (O + 23)).cost inp B s3 +
      ((seqs [lit (O + 19) 1, ar .sub (O + 18) (O + 5) (O + 19), ald (O + 18) PR (O + 18),
        lit (O + 17) q]).cost inp B s4 +
      ((ceilLogW (O + 17) (O + 18) (O + 18) (O + 23)).cost inp B s5 +
      (seqs [cp (O + 10) (O + 23), ar .add (O + 11) (O + 9) (O + 10)]).cost inp B s6))))) := rfl
  have hfr7 : ∀ r', r' ≠ O + 10 → r' ≠ O + 11 → s7.regs r' = s6.regs r' := fun r' a1 a2 => by
    simp (disch := omega) only [hs7, exec_seqs_cons, exec_seqs_nil, exec_cp, exec_ar,
      HS.setR_regs, upd_ne]
  have h10 : s7.regs (O + 10) = ceilLog q pa := by
    simp (disch := omega) only [hs7, exec_seqs_cons, exec_seqs_nil, exec_cp, exec_ar,
      HS.setR_regs, upd_ne, upd_eq, g1]
  have h11 : s7.regs (O + 11) = h1 + ceilLog q pa := by
    simp (disch := omega) only [hs7, exec_seqs_cons, exec_seqs_nil, exec_cp, exec_ar,
      HS.setR_regs, upd_ne, upd_eq, g1, g9, arith_add]
  have hmem7 : s7.mem = s4.mem := by
    rw [← g6mem]; simp only [hs7, exec_seqs_cons, exec_seqs_nil, exec_cp, exec_ar, HS.setR_mem]
  have harr : ∀ y i, s7.arr y i = s4.arr y i := fun y i => by simp only [HS.arr, hmem7]
  clear_value s1 s2 s3 s4 s5 s6 s7
  rw [hex]
  refine ⟨h10, h11, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [harr, p2 i (by rw [hMc]; exact lt_count_prime_of_le hi (by unfold primeBound; omega))]; rfl
  · intro y i hyi
    rw [harr, p3 y i hyi]
    have h3s : s3.mem = s.mem := by
      rw [hs3, exec_mem_of_stores inp _ rfl s2, hs2, exec_mem_of_stores inp _ rfl s1, hs1,
        exec_mem_of_stores inp _ rfl s]
    simp only [HS.arr, h3s]
  · intro r' h
    rw [hfr7 _ (by omega) (by omega), g3 _ (by omega), dfr _ (by omega) (by omega) (by omega),
      p4 _ (by omega), bfr _ (by omega) (by omega), f3 _ (by omega),
      afr _ (by omega) (by omega) (by omega)]
  · rw [← hex]; exact exec_cur_of_reads inp _ rfl s
  · rw [← hex]; exact exec_out_of_emits inp _ rfl s
  · rw [hco]
    have hf7 : (7 * (L + 2) + 4) * kappa B (RAM.bits M) ≤ (7 * Mc) * kappa B (RAM.bits M) :=
      Nat.mul_le_mul_right _ (by omega)
    have hg7 : (7 * pa + 9) * kappa B (RAM.bits M) ≤ (7 * Mc + 9) * kappa B (RAM.bits M) :=
      Nat.mul_le_mul_right _ (by omega)
    have hy : ((8 * Mc + 13) * (Mc + 1) + 14 * Mc + 40) * kappa B (RAM.bits M) =
      3 * kappa B (RAM.bits M) + (7 * Mc) * kappa B (RAM.bits M) + 6 * kappa B (RAM.bits M) +
      (8 * Mc + 13) * (Mc + 1) * kappa B (RAM.bits M) + 4 * kappa B (RAM.bits M) +
      (7 * Mc + 9) * kappa B (RAM.bits M) + 2 * kappa B (RAM.bits M) + 16 * kappa B (RAM.bits M) := by
      ring
    omega

end PartP

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.pPrime_spec_oai := @EditMulticoloring.Dev.Ram.pPrime_spec_oai
