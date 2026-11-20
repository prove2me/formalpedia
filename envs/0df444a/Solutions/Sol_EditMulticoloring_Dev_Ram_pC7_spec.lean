-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.pC7_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:37:03.157549+00:00
-- url     : https://prove2.me/submissions/2d17529a-2491-4667-b598-65edc8e30c76

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Construction
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000
import Theorems.Thm_EditMulticoloring_Dev_Ram_WordAt_congr
import Theorems.Thm_EditMulticoloring_Dev_Ram_goodW_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_kappa_bits_le
import Theorems.Thm_EditMulticoloring_Dev_Ram_pC8_spec
import Theorems.Thm_EditMulticoloring_Dev_Ram_upd_ne
import Theorems.Thm_EditMulticoloring_Dev_Ram_visits_le_visBound

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
-- module Solutions.EditMulticoloring.RamColor
/-!
# `localColor` on `Cmd` (q379, Part G): setup and neighbour-list facts

Register map of `colorOf` (base `g`, all registers `g .. g+50`; the enumerator `cfg` must
start at `cfg.r0 ≥ g + 51`):
* `g .. g+15` field context and scratch (`RamGF`), `g+16 g+17 g+18 g+19` = `D off K E` of
  `bitEvalW` (`D` is the digit array, `K` is kept there throughout);
* `g+24` `Q`, `g+25` `|x|`, `g+26` `J` (number of neighbours), `g+27` `α`, `g+28` `found`,
  `g+29` `ok`, `g+30` `bitEval(x,a)`, `g+31` `a`, `g+32` `j`, `g+33 g+35` loop `one`s,
  `g+34 g+36 g+38 g+39` scratch, `g+36` the result;
* `g+40 .. g+50` the block of the word utilities.
Arrays: `XA` (a copy of `x`), `DG` (digits: row `0` is `x`, row `m+1` neighbour `m`, stride `K`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ## The neighbour list -/

theorem mem_confusionNeighbors {q : ℕ} (t : ℕ) (x y : Word q) :
    y ∈ confusionNeighbors t x ↔ y ∈ nbrList t x := by
  unfold confusionNeighbors nbrList visits
  rw [List.mem_eraseDups, (List.mergeSort_perm _ _).mem_iff]

theorem confusionNeighbors_all {q : ℕ} (t : ℕ) (x : Word q) (f : Word q → Bool) :
    (confusionNeighbors t x).all f = (nbrList t x).all f := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  simp only [mem_confusionNeighbors]

theorem nbrList_length_le {q : ℕ} (t : ℕ) (x : Word q) :
    (nbrList t x).length ≤ (visits (2 * t) x).length := List.length_filter_le _ _

/-! ## Initialisation: field context, a copy of `x`, the digits of `value x` -/

/-! ## Enumeration: digits of every neighbour -/

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamColor3
/-!
# `colorOf`: the program computing `localColor t P p x` (q379, Part G)

Main theorem `colorOf_spec`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

theorem all_range_getD {α : Type*} (l : List α) (d : α) (f : α → Bool) :
    (List.range l.length).all (fun j => f (l.getD j d)) = l.all f := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  constructor
  · intro h y hy
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
    have := h j (by simpa using hj)
    rwa [List.getD_eq_getElem _ _ hj] at this
  · intro h j hj
    simp only [List.mem_range] at hj
    rw [List.getD_eq_getElem _ _ hj]; exact h _ (List.getElem_mem hj)

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamColor4
/-!
# `colorsAll`: the colour of `x` and of each of its neighbours (q379, Part G)

`colorsAll q t cfg1 cfg2 g X2 XA DG CLA`: `colorOf` (block `g .. g+50`, enumerator `cfg2`) on `x`
(result `g+51`), then the enumerator `cfg1` over `visits (2t) x`; for every visited `w` of length
`|x|` other than `x` (in visit order, duplicates kept: the list `nbrList t x`) it copies `w`
into `cfg2.buf (2t)`, runs `colorOf` and stores the colour at `CLA[J]`, `J := J + 1` (`g+52`).
Own registers `g+51 .. g+67`; `cfg2.r0 ≥ g + 68`, `cfg1.r0` above the registers of `cfg2`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-- The `.all` over the confusion neighbourhood, as a test over the indices of `nbrList`. -/
theorem confusionNeighbors_all_range {q : ℕ} (t : ℕ) (x : Word q) (f : Word q → Bool) :
    (confusionNeighbors t x).all f =
      (List.range (nbrList t x).length).all (fun j => f ((nbrList t x).getD j [])) := by
  rw [confusionNeighbors_all, all_range_getD]

/-! ## The program -/

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

/-! ## Counting the good indices below `i` -/

theorem countW_spec (r iR prR piR cxR vR CL : ℕ) (s : HS) (C Pm M : ℕ)
    (hi : iR < r ∨ r + 12 ≤ iR) (hpr : prR < r ∨ r + 12 ≤ prR) (hpi : piR < r ∨ r + 12 ≤ piR)
    (hcx : cxR < r ∨ r + 12 ≤ cxR) (hv : vR < r ∨ r + 12 ≤ vR)
    (hpi1 : piR ≠ iR) (hpi2 : piR ≠ prR) (hpi3 : piR ≠ cxR) (hpi4 : piR ≠ vR)
    (hC : ∀ ℓ < s.regs vR, s.arr CL ℓ ≤ C)
    (hP : ∀ i < s.regs iR, s.arr (s.regs prR) i ≤ Pm)
    (hM : CL + s.regs vR + C + s.regs cxR + Pm + s.regs iR + s.regs prR + 1 ≤ M) :
    ((countW r iR prR piR cxR vR CL).exec inp s).regs r =
      countGood (s.regs cxR) (s.arr (s.regs prR)) (s.arr CL) (s.regs vR) (s.regs iR) ∧
    (∀ r', (r' < r ∨ r + 12 ≤ r') → r' ≠ piR → ((countW r iR prR piR cxR vR CL).exec inp s).regs r' = s.regs r') ∧
    ((countW r iR prR piR cxR vR CL).exec inp s).mem = s.mem ∧
    ((countW r iR prR piR cxR vR CL).exec inp s).cur = s.cur ∧
    ((countW r iR prR piR cxR vR CL).exec inp s).out = s.out ∧
    (countW r iR prR piR cxR vR CL).cost inp B s ≤
      ((11 * s.regs vR + 11) * s.regs iR + 4) * kappa B (RAM.bits M) := by
  set I := s.regs iR
  set V := s.regs vR
  set cx := s.regs cxR
  set PRid := s.regs prR
  set s1 := s.setR r 0 with hs1
  have hn1 : s1.regs iR = I := by rw [hs1, HS.setR_regs, upd_ne (by omega)]
  have K := forLoop_spec inp B (r + 1) iR (r + 2)
    (seqs [ald piR prR (r + 1), goodW (r + 4) piR cxR vR CL, ar .add r r (r + 4)]) s1
    (by omega) (by omega)
    (fun k st => st.regs r = countGood cx (s.arr PRid) (s.arr CL) V k ∧
      (∀ r', (r' < r ∨ r + 12 ≤ r') → r' ≠ piR → st.regs r' = s.regs r') ∧ st.mem = s.mem)
    (fun _ => (11 * V + 8) * kappa B (RAM.bits M))
    ⟨by simp [countGood, hs1], fun r' h h' => by simp (disch := omega) [hs1, upd_ne], by simp [hs1]⟩
    (by
      intro k hk st ⟨hf, hr, hm⟩ hj
      rw [hn1] at hk
      have epr : st.regs prR = PRid := hr _ hpr hpi2.symm
      have ecx : st.regs cxR = cx := hr _ hcx hpi3.symm
      have ev : st.regs vR = V := hr _ hv hpi4.symm
      have hA : st.arr PRid k = s.arr PRid k := by simp [HS.arr, hm]
      set s2 := (ald piR prR (r + 1)).exec inp st with hs2
      have s2pi : s2.regs piR = s.arr PRid k := by
        simp [hs2, epr, hj, hA]
      have s2r : ∀ r', r' ≠ piR → s2.regs r' = st.regs r' := by
        intro r' h; simp (disch := omega) [hs2, upd_ne, h]
      have s2m : s2.mem = s.mem := by simp [hs2, hm]
      have hCs2 : ∀ ℓ < s2.regs vR, s2.arr CL ℓ ≤ C := by
        intro ℓ hℓ; rw [s2r _ hpi4.symm, ev] at hℓ
        have : s2.arr CL ℓ = s.arr CL ℓ := by simp [HS.arr, s2m]
        rw [this]; exact hC ℓ hℓ
      have hPk := hP k hk
      obtain ⟨g1, g2, g3, g4, g5, g6⟩ := goodW_spec inp B (r + 4) piR cxR vR CL s2 C M
        (by omega) (by omega) (by omega) hCs2
        (by rw [s2r _ hpi4.symm, s2r _ hpi3.symm, s2pi, ev, ecx]; omega)
      set s3 := (goodW (r + 4) piR cxR vR CL).exec inp s2 with hs3
      have hgood : goodP (s2.regs cxR) (s2.regs piR) (s2.arr CL) (s2.regs vR) =
          goodP cx (s.arr PRid k) (s.arr CL) V := by
        rw [s2r _ hpi4.symm, s2r _ hpi3.symm, s2pi, ev, ecx]
        congr 1; funext ℓ; simp [HS.arr, s2m]
      rw [hgood] at g1
      have hcnt : countGood cx (s.arr PRid) (s.arr CL) V (k + 1) =
          countGood cx (s.arr PRid) (s.arr CL) V k + (if goodP cx (s.arr PRid k) (s.arr CL) V then 1 else 0) := by
        unfold countGood
        rw [List.range_succ, List.filter_append, List.length_append]
        split_ifs with hg <;> simp [hg]
      have s3r : s3.regs r = countGood cx (s.arr PRid) (s.arr CL) V k := by
        rw [g2 _ (by omega), s2r _ (by omega), hf]
      have hcb : countGood cx (s.arr PRid) (s.arr CL) V k ≤ k := by
        unfold countGood; have := List.length_filter_le (fun i' => goodP cx (s.arr PRid i') (s.arr CL) V) (List.range k)
        simpa using this
      have hex : (seqs [ald piR prR (r + 1), goodW (r + 4) piR cxR vR CL, ar .add r r (r + 4)]).exec inp st =
          s3.setR r (s3.regs r + s3.regs (r + 4)) := rfl
      have hco : (seqs [ald piR prR (r + 1), goodW (r + 4) piR cxR vR CL, ar .add r r (r + 4)]).cost inp B st =
          kappa B (RAM.bits (st.regs prR + st.regs (r + 1) + st.arr (st.regs prR) (st.regs (r + 1)))) +
          ((goodW (r + 4) piR cxR vR CL).cost inp B s2 +
          (kappa B (RAM.bits (s3.regs r + s3.regs (r + 4))) + 0)) := rfl
      rw [hex, hco]
      refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩
      · simp (disch := omega) only [HS.setR_regs, upd_ne]; rw [g2 _ (by omega), s2r _ (by omega)]
        exact hj
      · rw [s3r, g1, hcnt]
        simp (disch := omega) only [HS.setR_regs, upd_ne, Function.update_self]
      · intro r' h h'
        simp (disch := omega) only [HS.setR_regs, upd_ne]
        rw [g2 _ (by omega), s2r _ h']; exact hr r' h h'
      · simp [g3, s2m]
      · rw [epr, hj, hA, s3r, g1]
        rw [s2r _ hpi4.symm, ev] at g6
        have e1 := kappa_bits_le B (a := PRid + k + s.arr PRid k) (M := M) (by omega)
        have e2 := kappa_bits_le B
          (a := countGood cx (s.arr PRid) (s.arr CL) V k + (if goodP cx (s.arr PRid k) (s.arr CL) V then 1 else 0))
          (M := M) (by split_ifs <;> omega)
        have : (11 * V + 8) * kappa B (RAM.bits M) = kappa B (RAM.bits M) +
          (11 * V + 6) * kappa B (RAM.bits M) + kappa B (RAM.bits M) := by ring
        omega)
  rw [hn1] at K
  obtain ⟨⟨k1, k2, k3⟩, k4⟩ := K
  have hcur : ((countW r iR prR piR cxR vR CL).exec inp s).cur = s.cur := exec_cur_of_reads inp _ rfl s
  have hout : ((countW r iR prR piR cxR vR CL).exec inp s).out = s.out := exec_out_of_emits inp _ rfl s
  refine ⟨k1, k2, k3, hcur, hout, ?_⟩
  have hc : (countW r iR prR piR cxR vR CL).cost inp B s = kappa B (RAM.bits 0) +
      (forLoop (r + 1) iR (r + 2)
        (seqs [ald piR prR (r + 1), goodW (r + 4) piR cxR vR CL, ar .add r r (r + 4)])).cost inp B s1 := rfl
  rw [hc]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at k4
  have := kappa_bits_le B (a := I) (M := M) (by omega)
  have := kappa_bits_le B (a := 0) (M := M) (by omega)
  nlinarith

/-! ## Writing `repr q w v` into an array -/

end Dec1

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

theorem pow_log_le_succ (q N : ℕ) : q ^ Nat.log q N ≤ N + 1 := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp
  · have := Nat.pow_log_le_self q h.ne'; omega

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

theorem params_J_le (q t n : ℕ) : (parameters q t n).J ≤ (parameters q t n).L / 2 + 1 :=
  pow_log_le_succ q _

theorem params_m_le (q t n : ℕ) : (parameters q t n).m ≤ n := Nat.sub_le _ _

end EditMulticoloring.Dev.Ram
end

section
-- module Solutions.EditMulticoloring.RamDecode2
/-!
# The decoder, part 2: semantics, layout, frames, and the last levels of the candidate test
(q379, Part D)

Layout of the decoder (constant registers / arrays; `t`-dependent ones are functions of `t`):
* registers `0` = n, `1` = 1 (the prime-table array id), `2` = done flag (`decFlag`),
  `3` = q^h₂, `4` = q, `100 .. 116` the parameters (`ParamsAt _ 100`), `200 .. 299` scratch of
  the candidate test, `400 ..` the `colorsAll` block (`g = 400`: `400` = p, `403` = W, `418` = K,
  `424` = Q), enumerators `dC2c` (`r0 = 470`), `dC1 t` (`r0 = 490 + 6t`), `dC0 t` (`r0 = 510 + 12t`);
* arrays `1` the prime table, `2` the result, `3 4 5 6` = `X2 XA DG CLA` of `colorsAll`, `10 ..`
  enumerator arrays, `dINV t = 18 + 5t` the inverse table of the short code.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ## Semantics of `validate` and `decode` -/

/-! ## Layout -/

theorem SFr.trans {t : ℕ} {s1 s2 s3 : HS} (h1 : SFr t s1 s2) (h2 : SFr t s2 s3) : SFr t s1 s3 :=
  ⟨fun r hr => (h2.1 r hr).trans (h1.1 r hr), fun y i hy => (h2.2.1 y i hy).trans (h1.2.1 y i hy),
    h2.2.2.1.trans h1.2.2.1, h2.2.2.2.trans h1.2.2.2⟩

theorem DOut.pre {q : ℕ} {t : ℕ} {st st1 st2 : HS} {res : Option (Word q)} (h1 : SFr t st st1)
    (h2 : st1.regs 2 = st.regs 2) (h : DOut t st1 st2 res) : DOut t st st2 res :=
  ⟨h1.trans h.1, fun hr => (h.2.1 hr).trans h2, h.2.2⟩

theorem DOut.none_of_SFr {q : ℕ} {t : ℕ} {st st' : HS} (h1 : SFr t st st')
    (h2 : st'.regs 2 = st.regs 2) : DOut (q := q) t st st' none :=
  ⟨h1, fun _ => h2, fun r hr => by cases hr⟩

theorem sfr_of_regs {t : ℕ} {st st' : HS} (hR : ∀ r, (KeptR t r ∨ r = 2) → st'.regs r = st.regs r)
    (hM : ∀ y i, KeptA t y → st'.arr y i = st.arr y i) (hc : st'.cur = st.cur)
    (ho : st'.out = st.out) : SFr t st st' ∧ st'.regs 2 = st.regs 2 :=
  ⟨⟨fun r hr => hR r (Or.inl hr), hM, hc, ho⟩, hR 2 (Or.inr rfl)⟩

theorem DCtx.of_SFr {q t n p : ℕ} {st st' : HS} (h : DCtx q t n p st) (hf : SFr t st st') :
    DCtx q t n p st' := by
  have R : ∀ r, r < 200 → r ≠ 2 → st'.regs r = st.regs r := fun r h1 h2 =>
    hf.1 r (Or.inl ⟨h1, h2⟩)
  have A1 : ∀ i, st'.arr 1 i = st.arr 1 i := fun i => hf.2.1 1 i (Or.inl rfl)
  have AI : ∀ i, st'.arr (dINV t) i = st.arr (dINV t) i := fun i =>
    hf.2.1 _ i (Or.inr (by unfold dINV; omega))
  obtain ⟨h0, h1, h3, h4, ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16⟩,
    g0, g3, g18, g24, prt, inv, invb⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (rw [R _ (by omega) (by omega)]; assumption)
    | (rw [hf.1 _ (by unfold KeptR; omega)]; assumption)
    | skip
  · intro i hi; rw [A1]; exact prt i hi
  · intro z hz; simp only [AI]; exact inv z hz
  · intro u hu; rw [AI]; exact invb u hu

/-! ## Size bounds -/

section Levels
variable (inp : ℕ → ℕ) (B : ℕ)

/-! ## Level 8: store the result `x ++ repr q (k - m) j` and set the done flag -/

/-! ## Level 7: count the good indices below `i`, compare with `J`, store -/

theorem goodP_eq_localGood {q : ℕ} (t : ℕ) (P : Parameters) (p : ℕ) (x : Word q) (i : ℕ)
    (cl : ℕ → ℕ) (hcl : ∀ ℓ (h : ℓ < (nbrList t x).length), cl ℓ = localColor t P p (nbrList t x)[ℓ]) :
    goodP (localColor t P p x) (primeAt i) cl (nbrList t x).length = localGood t P p x i := by
  unfold localGood goodP
  rw [confusionNeighbors_all_range]
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  apply forall_congr'; intro ℓ
  apply imp_congr_right; intro hℓ
  rw [List.mem_range] at hℓ
  rw [hcl ℓ hℓ, List.getD_eq_getElem _ _ hℓ]

theorem pC7_spec_oai {q t n p : ℕ} (hq : 2 ≤ q) (H3 : (parameters q t n).m + (parameters q t n).ρ = n)
    (hcol : ∀ y : Word q, localColor t (parameters q t n) p y < (parameters q t n).Q * (parameters q t n).Q + dTW q t n)
    (st : HS) (hc : DCtx q t n p st) (w : Word q) (hw : WordAt st (dC0 t).a0 0 w)
    (hwl : w.length = n) (i : ℕ) (hi : st.regs 213 = i) (hiL : i < (parameters q t n).L)
    (hcx : st.regs 451 = localColor t (parameters q t n) p (w.take (parameters q t n).m))
    (hV : st.regs 452 = (nbrList t (w.take (parameters q t n).m)).length)
    (hCL : ∀ ℓ (h : ℓ < (nbrList t (w.take (parameters q t n).m)).length),
      st.arr 6 ℓ = localColor t (parameters q t n) p (nbrList t (w.take (parameters q t n).m))[ℓ]) :
    DOut t st ((pC7 t).exec inp st)
      (if ((List.range i).filter (localGood t (parameters q t n) p (w.take (parameters q t n).m))).length
          ≥ (parameters q t n).J then none
       else some (w.take (parameters q t n).m ++ Code.repr q ((parameters q t n).k - (parameters q t n).m)
          ((List.range i).filter (localGood t (parameters q t n) p (w.take (parameters q t n).m))).length)) ∧
    (pC7 t).cost inp B st ≤ ((11 * dVb q t n + 11) * (parameters q t n).L + 7 * n + 7 * (parameters q t n).k + 40) *
      kappa B (RAM.bits (DM q t n)) := by
  set P := parameters q t n with hP
  set κ := kappa B (RAM.bits (DM q t n)) with hκ
  set x := w.take P.m with hx
  have kb : ∀ a, a ≤ DM q t n → kappa B (RAM.bits a) ≤ κ := fun a h => kappa_bits_le B h
  have hDM : DM q t n = 4 * q ^ n + 2 * q ^ P.h + 2 * (P.Q * P.Q) + 2 * dTW q t n + primeBound P.L +
    dVb q t n + P.L + 4 * n + P.k + 2 * q + 100 * t + 1000 := rfl
  have hmn : P.m ≤ n := params_m_le q t n
  have hxl : x.length = P.m := by rw [hx, List.length_take]; omega
  have hVb : (nbrList t x).length ≤ dVb q t n :=
    (nbrList_length_le t x).trans ((visits_le_visBound t x).trans (by rw [hxl]; exact le_rfl))
  have hJL : P.J ≤ P.L / 2 + 1 := params_J_le q t n
  have prt : ∀ i ≤ P.L, st.arr 1 i = primeAt i := hc.prt
  have hpb := le_primeBound P.L
  set j := ((List.range i).filter (localGood t P p x)).length with hj
  have hjle : j ≤ i := by
    have := List.length_filter_le (localGood t P p x) (List.range i); simp at this; omega
  -- countW
  have hcx0 := hcol x
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := countW_spec inp B 240 213 1 252 451 452 6 st
    (P.Q * P.Q + dTW q t n) (primeBound P.L) (DM q t n)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun ℓ hℓ => by
      rw [hV] at hℓ; rw [hCL ℓ hℓ]; exact (hcol _).le)
    (fun i' hi' => by
      rw [hc.pr1, prt i' (by rw [hi] at hi'; omega)]
      exact (primeAt_lt_primeBound (L := P.L) (by rw [hi] at hi'; omega)).le)
    (by rw [hV, hcx, hi, hc.pr1]; omega)
  rw [hcx, hc.pr1, hV, hi] at k1
  rw [hV, hi] at k6
  set s1 := (countW 240 213 1 252 451 452 6).exec inp st with hs1
  have hcount : s1.regs 240 = j := by
    rw [k1, hj]
    unfold countGood
    congr 1
    apply List.filter_congr
    intro i' hi'
    rw [List.mem_range] at hi'
    have hpr : st.arr 1 i' = primeAt i' := prt i' (by omega)
    have : st.arr 1 = fun i'' => st.arr 1 i'' := rfl
    simp only [hpr]
    exact goodP_eq_localGood t P p x i' (st.arr 6) hCL
  set s2 := s1.setR 212 (if s1.regs 240 < s1.regs 108 then 1 else 0) with hs2
  have hfr2 := sfr_of_regs (t := t) (st := st) (st' := s2)
    (fun r hr => by
      unfold KeptR at hr
      simp only [hs2, HS.setR_regs]; rw [upd_ne (by omega), k2 r (by omega) (by omega)])
    (fun y i _ => by simp [hs2, HS.arr, k3]) (by simp [hs2, k4]) (by simp [hs2, k5])
  have e108 : s1.regs 108 = P.J := by rw [k2 _ (by omega) (by omega)]; exact hc.par.hJ
  have v212 : s2.regs 212 = if j < P.J then 1 else 0 := by
    simp [hs2, hcount, e108]
  have hex : (pC7 t).exec inp st = (Cmd.ifz 212 .skip (pC8 t)).exec inp s2 := rfl
  have hco : (pC7 t).cost inp B st = (countW 240 213 1 252 451 452 6).cost inp B st +
      ((ar .lt 212 240 108).cost inp B s1 + ((Cmd.ifz 212 .skip (pC8 t)).cost inp B s2 + 0)) := rfl
  have c2 : (ar .lt 212 240 108).cost inp B s1 ≤ κ := by
    simp only [cost_ar]; rw [hcount, e108]; exact kb _ (by omega)
  have c1 : (countW 240 213 1 252 451 452 6).cost inp B st ≤ ((11 * dVb q t n + 11) * P.L + 4) * κ := by
    refine k6.trans (Nat.mul_le_mul_right _ ?_)
    have : (11 * (nbrList t x).length + 11) * i ≤ (11 * dVb q t n + 11) * P.L :=
      Nat.mul_le_mul (by omega) hiL.le
    omega
  have hk0 := kb 0 (by omega)
  have hk1 := kb 1 (by omega)
  rw [hex, hco]
  by_cases hjJ : j < P.J
  · have hz : s2.regs 212 ≠ 0 := by rw [v212, if_pos hjJ]; omega
    have hc2 := hc.of_SFr hfr2.1
    have hw2 : WordAt s2 (dC0 t).a0 0 w := hw.congr (fun i _ => hfr2.1.2.1 _ _ (Or.inr (by simp [dC0])))
    obtain ⟨D1, D2⟩ := pC8_spec inp B hq H3 s2 hc2 w hw2 hwl j
      (by rw [show s2.regs 240 = s1.regs 240 by simp [hs2], hcount]) (show j ≤ P.L by omega)
    have D2' : (pC8 t).cost inp B s2 ≤ (7 * n + 7 * P.k + 30) * κ := D2
    rw [if_neg (by omega)]
    refine ⟨?_, ?_⟩
    · rw [exec_ifz, if_neg hz]; exact DOut.pre hfr2.1 hfr2.2 D1
    · rw [cost_ifz, if_neg hz]
      have := kb (s2.regs 212) (by rw [v212]; split_ifs <;> omega)
      have h3 : ((11 * dVb q t n + 11) * P.L + 7 * n + 7 * P.k + 40) * κ =
        ((11 * dVb q t n + 11) * P.L + 4) * κ + κ + κ + (7 * n + 7 * P.k + 30) * κ + 4 * κ := by ring
      rw [h3]; omega
  · have hz : s2.regs 212 = 0 := by rw [v212, if_neg hjJ]
    rw [if_pos (by omega)]
    refine ⟨?_, ?_⟩
    · rw [exec_ifz, if_pos hz]; exact DOut.none_of_SFr hfr2.1 hfr2.2
    · rw [cost_ifz, if_pos hz, cost_skip, hz]
      have h3 : ((11 * dVb q t n + 11) * P.L + 7 * n + 7 * P.k + 40) * κ =
        ((11 * dVb q t n + 11) * P.L + 4) * κ + κ + (7 * n + 7 * P.k + 35) * κ := by ring
      rw [h3]
      have : κ ≤ (7 * n + 7 * P.k + 35) * κ := Nat.le_mul_of_pos_left _ (by omega)
      omega

/-! ## Level 6: compare `η` with the colour of `x` modulo `primeAt i` -/

/-! ## Level 5: the colours (`colorsAll`), the test `localGood x i` -/

/-! ## Level 4: `pi := PR[i]`, test `η < pi` -/

/-! ## Level 3: `i := idx / q^h₂`, `η := idx % q^h₂`, test `i < L` -/

/-! ## Level 2: `idx := INV - 1`, test `idx < q^h` -/

/-! ## The candidate test: value of the tail, `INV` lookup -/

end Levels

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.pC7_spec_oai := @EditMulticoloring.Dev.Ram.pC7_spec_oai
