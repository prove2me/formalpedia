-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.goodW_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:34:53.110177+00:00
-- url     : https://prove2.me/submissions/af4cca4f-a373-4da3-af4e-aa10203cba92

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
-- module Solutions.EditMulticoloring.RamDecode
/-!
# The decoder, part 1: good-index test, good-index count, writing `repr` (q379, Part D)

* `goodW r piR cxR vR CL`: `regs r := 1` iff `cx % pi ≠ CL[ℓ] % pi` for all `ℓ < V`
  (`pi = regs piR`, `cx = regs cxR`, `V = regs vR`); writes only `r .. r+7`.
* `countW r iR prR piR cxR vR CL`: `regs r := #{i' < regs iR : goodW-test with pi = PR[i']}`;
  writes only `r .. r+3`, `piR`, and the `goodW` block `r+4 .. r+11`.
* `reprOut r vR wR offR X qR`: writes `repr q w v` into array `X` at offset `off`;
  writes only `r .. r+6`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

section Dec1
variable (inp : ℕ → ℕ) (B : ℕ)

/-! ## The good-index test -/

theorem goodW_spec_oai (r piR cxR vR CL : ℕ) (s : HS) (C M : ℕ)
    (hpi : piR < r ∨ r + 8 ≤ piR) (hcx : cxR < r ∨ r + 8 ≤ cxR) (hv : vR < r ∨ r + 8 ≤ vR)
    (hC : ∀ ℓ < s.regs vR, s.arr CL ℓ ≤ C)
    (hM : CL + s.regs vR + C + s.regs cxR + s.regs piR + 1 ≤ M) :
    ((goodW r piR cxR vR CL).exec inp s).regs r =
      (if goodP (s.regs cxR) (s.regs piR) (s.arr CL) (s.regs vR) then 1 else 0) ∧
    (∀ r', (r' < r ∨ r + 8 ≤ r') → ((goodW r piR cxR vR CL).exec inp s).regs r' = s.regs r') ∧
    ((goodW r piR cxR vR CL).exec inp s).mem = s.mem ∧
    ((goodW r piR cxR vR CL).exec inp s).cur = s.cur ∧
    ((goodW r piR cxR vR CL).exec inp s).out = s.out ∧
    (goodW r piR cxR vR CL).cost inp B s ≤ (11 * s.regs vR + 6) * kappa B (RAM.bits M) := by
  set pi := s.regs piR
  set cx := s.regs cxR
  set V := s.regs vR
  set s1 := (seqs [lit r 1, ar .mod (r + 1) cxR piR, lit (r + 2) CL]).exec inp s with hs1
  have r1 : ∀ r', (r' < r ∨ r + 8 ≤ r') → s1.regs r' = s.regs r' := by
    intro r' h; simp (disch := omega) [hs1, upd_ne]
  have v0 : s1.regs r = 1 := by simp (disch := omega) [hs1, upd_ne]
  have v1 : s1.regs (r + 1) = cx % pi := by simp (disch := omega) [hs1, upd_ne, cx, pi]
  have v2 : s1.regs (r + 2) = CL := by simp (disch := omega) [hs1, upd_ne]
  have m1 : s1.mem = s.mem := by simp [hs1]
  have hn1 : s1.regs vR = V := r1 _ hv
  have c1 : (seqs [lit r 1, ar .mod (r + 1) cxR piR, lit (r + 2) CL]).cost inp B s ≤
      3 * kappa B (RAM.bits M) := by
    simp (disch := omega) only [cost_seqs_cons, cost_seqs_nil, cost_lit, cost_ar, exec_seqs_cons,
      exec_lit, HS.setR_regs, upd_ne]
    have := kappa_bits_le B (a := 1) (M := M) (by omega)
    have := kappa_bits_le B (a := s.regs cxR + s.regs piR) (M := M) (by omega)
    have := kappa_bits_le B (a := CL) (M := M) (by omega)
    omega
  have K := forLoop_spec inp B (r + 3) vR (r + 4) (goodBody r piR) s1
    (by omega) (by omega)
    (fun k st => st.regs r = (if goodP cx pi (s.arr CL) k then 1 else 0) ∧
      st.regs (r + 1) = cx % pi ∧ st.regs (r + 2) = CL ∧
      (∀ r', (r' < r ∨ r + 8 ≤ r') → st.regs r' = s.regs r') ∧ st.mem = s.mem)
    (fun _ => 8 * kappa B (RAM.bits M))
    ⟨by simp (disch := omega) [upd_ne, v0, goodP], by simp (disch := omega) [upd_ne, v1],
      by simp (disch := omega) [upd_ne, v2], fun r' h => by simp (disch := omega) [upd_ne, r1 r' h],
      by simp [m1]⟩
    (by
      intro k hk st ⟨hf, h1, h2, hr, hm⟩ hj
      rw [hn1] at hk
      have epi : st.regs piR = pi := hr _ hpi
      have hA : st.arr CL k = s.arr CL k := by simp [HS.arr, hm]
      have hCk := hC k hk
      set A := s.arr CL k
      have hg : goodP cx pi (s.arr CL) (k + 1) = (goodP cx pi (s.arr CL) k && decide (cx % pi ≠ A % pi)) := by
        simp [goodP, List.range_succ, List.all_append, A]
      simp (disch := omega) only [goodBody, exec_seqs_cons, exec_seqs_nil, exec_ar, exec_ald, exec_ifz,
        exec_skip, exec_lit, arith_add, arith_sub, arith_mod, HS.setR_regs, HS.setR_arr, HS.setR_mem,
        upd_ne, upd_eq, h1, h2, epi, hj, hA, cost_seqs_cons, cost_seqs_nil, cost_ar,
        cost_ald, cost_ifz, cost_lit, cost_skip]
      have hmod1 : A % pi ≤ A := Nat.mod_le _ _
      have hmod2 : cx % pi ≤ cx := Nat.mod_le _ _
      have e2 := kappa_bits_le B (a := CL + k + A) (M := M) (by omega)
      have e3 := kappa_bits_le B (a := A + pi) (M := M) (by omega)
      have e4 := kappa_bits_le B (a := A % pi + cx % pi) (M := M) (by omega)
      have e5 := kappa_bits_le B (a := cx % pi + A % pi) (M := M) (by omega)
      have e6 := kappa_bits_le B (a := A % pi - cx % pi + (cx % pi - A % pi)) (M := M) (by omega)
      have e7 := kappa_bits_le B (a := A % pi - cx % pi + (cx % pi - A % pi)) (M := M) (by omega)
      have e8 := kappa_bits_le B (a := 0) (M := M) (by omega)
      by_cases hz : A % pi - cx % pi + (cx % pi - A % pi) = 0
      · have hAB' : cx % pi = A % pi := by omega
        simp only [hz, if_true]
        refine ⟨by simp (disch := omega) [upd_ne, hj], ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · simp (disch := omega) only [upd_ne, upd_eq, HS.setR_regs, hg]; simp [hAB']
        · simp (disch := omega) only [upd_ne, HS.setR_regs]; exact h1
        · simp (disch := omega) only [upd_ne, HS.setR_regs]; exact h2
        · intro r' h
          simp (disch := omega) only [upd_ne, HS.setR_regs]; exact hr r' h
        · simpa using hm
        · omega
      · have hAB' : cx % pi ≠ A % pi := by omega
        simp only [hz, if_false]
        refine ⟨by simp (disch := omega) [upd_ne, hj], ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · simp (disch := omega) only [upd_ne, upd_eq, HS.setR_regs, hg]; rw [hf]; simp [hAB']
        · simp (disch := omega) only [upd_ne, HS.setR_regs]; exact h1
        · simp (disch := omega) only [upd_ne, HS.setR_regs]; exact h2
        · intro r' h
          simp (disch := omega) only [upd_ne, HS.setR_regs]; exact hr r' h
        · simpa using hm
        · omega)
  rw [hn1] at K
  obtain ⟨⟨k1, -, -, k2, k3⟩, k4⟩ := K
  have hcur : ((goodW r piR cxR vR CL).exec inp s).cur = s.cur := exec_cur_of_reads inp _ rfl s
  have hout : ((goodW r piR cxR vR CL).exec inp s).out = s.out := exec_out_of_emits inp _ rfl s
  refine ⟨k1, k2, k3, hcur, hout, ?_⟩
  have hc : (goodW r piR cxR vR CL).cost inp B s =
      (seqs [lit r 1, ar .mod (r + 1) cxR piR, lit (r + 2) CL]).cost inp B s +
      (forLoop (r + 3) vR (r + 4) (goodBody r piR)).cost inp B s1 := rfl
  rw [hc]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at k4
  have := kappa_bits_le B (a := V) (M := M) (by omega)
  nlinarith

/-! ## Counting the good indices below `i` -/

/-! ## Writing `repr q w v` into an array -/

end Dec1

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.goodW_spec_oai := @EditMulticoloring.Dev.Ram.goodW_spec_oai
