-- Prove2me | solution 1 for Freiman.late_witnesses_0555_0740
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-12T05:43:27.474394+00:00
-- url     : https://prove2.me/submissions/ce52ceaa-157b-436e-be3a-43d9be5131f9

import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic

set_option maxRecDepth 8000
set_option maxHeartbeats 0

open Freiman
set_option linter.all false

/- ===================================================================
   The global witness array `lateCatalog.witnesses` is the concatenation
   `lateWitnessData1 ++ ... ++ lateWitnessData8` (sizes 185x7 + 178 = 1473).
   For this leaf (global index range [555,740)) every witness lives in
   block `lateWitnessData4` alone, so we avoid ever forcing the kernel to reduce the
   8-way concatenation: `hidx` peels the concatenation down to this one
   block via a direct chain of `Array.getElem?_append_left/right` steps
   (only the size facts on the path to this block, not a generic
   `simp [Array.getElem?_append]; split_ifs` over the whole structure --
   that generic form was measured to dominate runtime by 1-2 orders of
   magnitude). Each certificate-check chunk is materialized ONCE via
   `toList.drop/take` (avoiding O(index) repeated re-walks of the
   array-as-list) and checked by a single `decide +kernel` call.
   =================================================================== -/

theorem sD1 : lateWitnessData1.size = 185 := by decide
theorem sD2 : lateWitnessData2.size = 185 := by decide
theorem sD3 : lateWitnessData3.size = 185 := by decide
theorem sD4 : lateWitnessData4.size = 185 := by decide
theorem sD5 : lateWitnessData5.size = 185 := by decide
theorem sD6 : lateWitnessData6.size = 185 := by decide
theorem sD7 : lateWitnessData7.size = 185 := by decide
theorem sD8 : lateWitnessData8.size = 178 := by decide

theorem s2 : (lateWitnessData1 ++ lateWitnessData2).size = 370 := by
  rw [Array.size_append, sD1, sD2]
theorem s3 : (lateWitnessData1 ++ lateWitnessData2 ++ lateWitnessData3).size = 555 := by
  rw [Array.size_append, s2, sD3]
theorem s4 : (lateWitnessData1 ++ lateWitnessData2 ++ lateWitnessData3 ++ lateWitnessData4).size = 740 := by
  rw [Array.size_append, s3, sD4]
theorem s5 : (lateWitnessData1 ++ lateWitnessData2 ++ lateWitnessData3 ++ lateWitnessData4 ++ lateWitnessData5).size = 925 := by
  rw [Array.size_append, s4, sD5]
theorem s6 : (lateWitnessData1 ++ lateWitnessData2 ++ lateWitnessData3 ++ lateWitnessData4 ++ lateWitnessData5 ++ lateWitnessData6).size = 1110 := by
  rw [Array.size_append, s5, sD6]
theorem s7 : (lateWitnessData1 ++ lateWitnessData2 ++ lateWitnessData3 ++ lateWitnessData4 ++ lateWitnessData5 ++ lateWitnessData6 ++ lateWitnessData7).size = 1295 := by
  rw [Array.size_append, s6, sD7]

theorem hidx : ∀ i : ℕ, 555 ≤ i → i < 740 →
    lateCatalog.witnesses[i]? = lateWitnessData4[i - 555]? := by
  intro i hlo hhi
  show (lateWitnessData1 ++ lateWitnessData2 ++ lateWitnessData3 ++ lateWitnessData4 ++
    lateWitnessData5 ++ lateWitnessData6 ++ lateWitnessData7 ++ lateWitnessData8)[i]? = _
  rw [Array.getElem?_append_left (by rw [s7]; omega), Array.getElem?_append_left (by rw [s6]; omega), Array.getElem?_append_left (by rw [s5]; omega), Array.getElem?_append_left (by rw [s4]; omega), Array.getElem?_append_right (by rw [s3]; omega), s3]

abbrev rdflt : LateWitnessRow := ⟨0,0,0,fun _ _ => 0⟩

def lateWitnessOf (r : LateWitnessRow) : CertWitness :=
  let l := lateBound lateCatalog r.lower
  let u := lateBound lateCatalog r.upper
  let R := lateRectangle lateCatalog r.rectangle
  ⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, r.lowerBounds⟩

theorem lateWitness_eq (i : ℕ) (r : LateWitnessRow) (h : (lateCatalog.witnesses[i]?).getD rdflt = r) :
    lateWitness lateCatalog (i+1) = lateWitnessOf r := by
  unfold lateWitness lateWitnessRow lateWitnessOf
  rw [Nat.add_sub_cancel]
  simp only [h]

def fcRect (R : CertRectangle) : Bool :=
  decide (R.r0 < R.r1) && decide (R.s0 < R.s1) && decide (0 ≤ R.r0)
def fcThr (t : CertThreshold) : Bool :=
  decide (0 ≤ certFieldLower t.x0) && decide (0 ≤ certFieldLower t.x1)
def fcCBV (z : CertField) (q : ℚ) : Bool :=
  decide (0 ≤ q) && (if q = 0 then decide (0 ≤ certFieldLower z) else decide (q < certFieldLower z))
def fcCBVs (C : CertPoly22) (L : Fin 3 → Fin 3 → ℚ) : Bool :=
  fcCBV (C 0 0) (L 0 0) && fcCBV (C 0 1) (L 0 1) && fcCBV (C 0 2) (L 0 2) &&
  fcCBV (C 1 0) (L 1 0) && fcCBV (C 1 1) (L 1 1) && fcCBV (C 1 2) (L 1 2) &&
  fcCBV (C 2 0) (L 2 0) && fcCBV (C 2 1) (L 2 1) && fcCBV (C 2 2) (L 2 2)
def fcPos (L : Fin 3 → Fin 3 → ℚ) : Bool :=
  decide (0 < L 0 0) && decide (0 < L 0 1) && decide (0 < L 0 2) &&
  decide (0 < L 1 0) && decide (0 < L 1 1) && decide (0 < L 1 2) &&
  decide (0 < L 2 0) && decide (0 < L 2 1) && decide (0 < L 2 2)
def fcRest (w : CertWitness) : Bool :=
  w.lowerBound.lower && !w.upperBound.lower && fcRect w.rectangle &&
  fcThr w.lowerBound.threshold && fcThr w.upperBound.threshold &&
  (fcPos w.lowerBounds || w.lowerBound.strict || w.upperBound.strict)
def fcAll (r : LateWitnessRow) : Bool :=
  let w := lateWitnessOf r
  fcRest w && fcCBVs w.coefficients w.lowerBounds

theorem fcRect_imp {R : CertRectangle} (h : fcRect R = true) :
    certRectangleValid R ∧ 0 ≤ R.r0 := by
  unfold fcRect at h; unfold certRectangleValid
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨⟨h.1.1, h.1.2⟩, h.2⟩

theorem fcThr_imp {t : CertThreshold} (h : fcThr t = true) : certThresholdDataValid t := by
  unfold fcThr at h; unfold certThresholdDataValid
  simpa using h

theorem fcCBV_imp {z : CertField} {q : ℚ} (h : fcCBV z q = true) : certCoefficientBoundValid z q := by
  unfold fcCBV at h
  unfold certCoefficientBoundValid
  by_cases hq : q = 0 <;> simp_all

theorem fcCBVs_imp {C : CertPoly22} {L : Fin 3 → Fin 3 → ℚ} (h : fcCBVs C L = true) :
    ∀ i j : Fin 3, certCoefficientBoundValid (C i j) (L i j) := by
  unfold fcCBVs at h
  simp only [Bool.and_eq_true] at h
  intro i j
  fin_cases i <;> fin_cases j <;> first
    | exact fcCBV_imp h.1.1.1.1.1.1.1.1
    | exact fcCBV_imp h.1.1.1.1.1.1.1.2
    | exact fcCBV_imp h.1.1.1.1.1.1.2
    | exact fcCBV_imp h.1.1.1.1.1.2
    | exact fcCBV_imp h.1.1.1.1.2
    | exact fcCBV_imp h.1.1.1.2
    | exact fcCBV_imp h.1.1.2
    | exact fcCBV_imp h.1.2
    | exact fcCBV_imp h.2

theorem fcPos_imp {L : Fin 3 → Fin 3 → ℚ} (h : fcPos L = true) : ∀ i j : Fin 3, 0 < L i j := by
  unfold fcPos at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  intro i j
  fin_cases i <;> fin_cases j <;> tauto

theorem fcRest_imp {w : CertWitness} (h : fcRest w = true) :
    w.lowerBound.lower = true ∧ w.upperBound.lower = false ∧
    certRectangleValid w.rectangle ∧ 0 ≤ w.rectangle.r0 ∧
    certThresholdDataValid w.lowerBound.threshold ∧
    certThresholdDataValid w.upperBound.threshold ∧
    ((∀ i j : Fin 3, 0 < w.lowerBounds i j) ∨ w.lowerBound.strict = true ∨ w.upperBound.strict = true) := by
  unfold fcRest at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨h1,h2⟩,h3⟩,h4⟩,h5⟩,h6⟩ := h
  refine ⟨h1, h2, (fcRect_imp h3).1, (fcRect_imp h3).2, fcThr_imp h4, fcThr_imp h5, ?_⟩
  rcases h6 with (h6 | h6) | h6
  · exact Or.inl (fcPos_imp h6)
  · exact Or.inr (Or.inl h6)
  · exact Or.inr (Or.inr h6)

theorem fcAll_imp {r : LateWitnessRow} (h : fcAll r = true) : certWitnessValid (lateWitnessOf r) := by
  unfold fcAll at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨e1,e2,e3,e4,e5,e6,e7⟩ := fcRest_imp h.1
  exact ⟨e1,e2,e3,e4,e5,e6, rfl, fcCBVs_imp h.2, e7⟩

theorem batch1 : ∀ r ∈ (lateWitnessData4.toList.drop 0).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey1 : ∀ j, 0 ≤ j → j < 4 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch1
  apply List.mem_of_getElem? (i := j - 0)
  rw [List.getElem?_take_of_lt (show j - 0 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 0 + (j - 0) = j by omega, h1]
  rfl

theorem batch2 : ∀ r ∈ (lateWitnessData4.toList.drop 4).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey2 : ∀ j, 4 ≤ j → j < 8 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch2
  apply List.mem_of_getElem? (i := j - 4)
  rw [List.getElem?_take_of_lt (show j - 4 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 4 + (j - 4) = j by omega, h1]
  rfl

theorem batch3 : ∀ r ∈ (lateWitnessData4.toList.drop 8).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey3 : ∀ j, 8 ≤ j → j < 12 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch3
  apply List.mem_of_getElem? (i := j - 8)
  rw [List.getElem?_take_of_lt (show j - 8 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 8 + (j - 8) = j by omega, h1]
  rfl

theorem batch4 : ∀ r ∈ (lateWitnessData4.toList.drop 12).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey4 : ∀ j, 12 ≤ j → j < 16 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch4
  apply List.mem_of_getElem? (i := j - 12)
  rw [List.getElem?_take_of_lt (show j - 12 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 12 + (j - 12) = j by omega, h1]
  rfl

theorem batch5 : ∀ r ∈ (lateWitnessData4.toList.drop 16).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey5 : ∀ j, 16 ≤ j → j < 20 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch5
  apply List.mem_of_getElem? (i := j - 16)
  rw [List.getElem?_take_of_lt (show j - 16 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 16 + (j - 16) = j by omega, h1]
  rfl

theorem batch6 : ∀ r ∈ (lateWitnessData4.toList.drop 20).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey6 : ∀ j, 20 ≤ j → j < 24 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch6
  apply List.mem_of_getElem? (i := j - 20)
  rw [List.getElem?_take_of_lt (show j - 20 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 20 + (j - 20) = j by omega, h1]
  rfl

theorem batch7 : ∀ r ∈ (lateWitnessData4.toList.drop 24).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey7 : ∀ j, 24 ≤ j → j < 28 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch7
  apply List.mem_of_getElem? (i := j - 24)
  rw [List.getElem?_take_of_lt (show j - 24 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 24 + (j - 24) = j by omega, h1]
  rfl

theorem batch8 : ∀ r ∈ (lateWitnessData4.toList.drop 28).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey8 : ∀ j, 28 ≤ j → j < 32 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch8
  apply List.mem_of_getElem? (i := j - 28)
  rw [List.getElem?_take_of_lt (show j - 28 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 28 + (j - 28) = j by omega, h1]
  rfl

theorem batch9 : ∀ r ∈ (lateWitnessData4.toList.drop 32).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey9 : ∀ j, 32 ≤ j → j < 36 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch9
  apply List.mem_of_getElem? (i := j - 32)
  rw [List.getElem?_take_of_lt (show j - 32 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 32 + (j - 32) = j by omega, h1]
  rfl

theorem batch10 : ∀ r ∈ (lateWitnessData4.toList.drop 36).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey10 : ∀ j, 36 ≤ j → j < 40 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch10
  apply List.mem_of_getElem? (i := j - 36)
  rw [List.getElem?_take_of_lt (show j - 36 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 36 + (j - 36) = j by omega, h1]
  rfl

theorem batch11 : ∀ r ∈ (lateWitnessData4.toList.drop 40).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey11 : ∀ j, 40 ≤ j → j < 44 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch11
  apply List.mem_of_getElem? (i := j - 40)
  rw [List.getElem?_take_of_lt (show j - 40 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 40 + (j - 40) = j by omega, h1]
  rfl

theorem batch12 : ∀ r ∈ (lateWitnessData4.toList.drop 44).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey12 : ∀ j, 44 ≤ j → j < 48 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch12
  apply List.mem_of_getElem? (i := j - 44)
  rw [List.getElem?_take_of_lt (show j - 44 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 44 + (j - 44) = j by omega, h1]
  rfl

theorem batch13 : ∀ r ∈ (lateWitnessData4.toList.drop 48).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey13 : ∀ j, 48 ≤ j → j < 52 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch13
  apply List.mem_of_getElem? (i := j - 48)
  rw [List.getElem?_take_of_lt (show j - 48 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 48 + (j - 48) = j by omega, h1]
  rfl

theorem batch14 : ∀ r ∈ (lateWitnessData4.toList.drop 52).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey14 : ∀ j, 52 ≤ j → j < 56 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch14
  apply List.mem_of_getElem? (i := j - 52)
  rw [List.getElem?_take_of_lt (show j - 52 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 52 + (j - 52) = j by omega, h1]
  rfl

theorem batch15 : ∀ r ∈ (lateWitnessData4.toList.drop 56).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey15 : ∀ j, 56 ≤ j → j < 60 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch15
  apply List.mem_of_getElem? (i := j - 56)
  rw [List.getElem?_take_of_lt (show j - 56 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 56 + (j - 56) = j by omega, h1]
  rfl

theorem batch16 : ∀ r ∈ (lateWitnessData4.toList.drop 60).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey16 : ∀ j, 60 ≤ j → j < 64 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch16
  apply List.mem_of_getElem? (i := j - 60)
  rw [List.getElem?_take_of_lt (show j - 60 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 60 + (j - 60) = j by omega, h1]
  rfl

theorem batch17 : ∀ r ∈ (lateWitnessData4.toList.drop 64).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey17 : ∀ j, 64 ≤ j → j < 68 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch17
  apply List.mem_of_getElem? (i := j - 64)
  rw [List.getElem?_take_of_lt (show j - 64 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 64 + (j - 64) = j by omega, h1]
  rfl

theorem batch18 : ∀ r ∈ (lateWitnessData4.toList.drop 68).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey18 : ∀ j, 68 ≤ j → j < 72 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch18
  apply List.mem_of_getElem? (i := j - 68)
  rw [List.getElem?_take_of_lt (show j - 68 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 68 + (j - 68) = j by omega, h1]
  rfl

theorem batch19 : ∀ r ∈ (lateWitnessData4.toList.drop 72).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey19 : ∀ j, 72 ≤ j → j < 76 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch19
  apply List.mem_of_getElem? (i := j - 72)
  rw [List.getElem?_take_of_lt (show j - 72 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 72 + (j - 72) = j by omega, h1]
  rfl

theorem batch20 : ∀ r ∈ (lateWitnessData4.toList.drop 76).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey20 : ∀ j, 76 ≤ j → j < 80 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch20
  apply List.mem_of_getElem? (i := j - 76)
  rw [List.getElem?_take_of_lt (show j - 76 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 76 + (j - 76) = j by omega, h1]
  rfl

theorem batch21 : ∀ r ∈ (lateWitnessData4.toList.drop 80).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey21 : ∀ j, 80 ≤ j → j < 84 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch21
  apply List.mem_of_getElem? (i := j - 80)
  rw [List.getElem?_take_of_lt (show j - 80 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 80 + (j - 80) = j by omega, h1]
  rfl

theorem batch22 : ∀ r ∈ (lateWitnessData4.toList.drop 84).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey22 : ∀ j, 84 ≤ j → j < 88 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch22
  apply List.mem_of_getElem? (i := j - 84)
  rw [List.getElem?_take_of_lt (show j - 84 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 84 + (j - 84) = j by omega, h1]
  rfl

theorem batch23 : ∀ r ∈ (lateWitnessData4.toList.drop 88).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey23 : ∀ j, 88 ≤ j → j < 92 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch23
  apply List.mem_of_getElem? (i := j - 88)
  rw [List.getElem?_take_of_lt (show j - 88 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 88 + (j - 88) = j by omega, h1]
  rfl

theorem batch24 : ∀ r ∈ (lateWitnessData4.toList.drop 92).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey24 : ∀ j, 92 ≤ j → j < 96 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch24
  apply List.mem_of_getElem? (i := j - 92)
  rw [List.getElem?_take_of_lt (show j - 92 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 92 + (j - 92) = j by omega, h1]
  rfl

theorem batch25 : ∀ r ∈ (lateWitnessData4.toList.drop 96).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey25 : ∀ j, 96 ≤ j → j < 100 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch25
  apply List.mem_of_getElem? (i := j - 96)
  rw [List.getElem?_take_of_lt (show j - 96 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 96 + (j - 96) = j by omega, h1]
  rfl

theorem batch26 : ∀ r ∈ (lateWitnessData4.toList.drop 100).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey26 : ∀ j, 100 ≤ j → j < 104 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch26
  apply List.mem_of_getElem? (i := j - 100)
  rw [List.getElem?_take_of_lt (show j - 100 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 100 + (j - 100) = j by omega, h1]
  rfl

theorem batch27 : ∀ r ∈ (lateWitnessData4.toList.drop 104).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey27 : ∀ j, 104 ≤ j → j < 108 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch27
  apply List.mem_of_getElem? (i := j - 104)
  rw [List.getElem?_take_of_lt (show j - 104 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 104 + (j - 104) = j by omega, h1]
  rfl

theorem batch28 : ∀ r ∈ (lateWitnessData4.toList.drop 108).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey28 : ∀ j, 108 ≤ j → j < 112 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch28
  apply List.mem_of_getElem? (i := j - 108)
  rw [List.getElem?_take_of_lt (show j - 108 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 108 + (j - 108) = j by omega, h1]
  rfl

theorem batch29 : ∀ r ∈ (lateWitnessData4.toList.drop 112).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey29 : ∀ j, 112 ≤ j → j < 116 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch29
  apply List.mem_of_getElem? (i := j - 112)
  rw [List.getElem?_take_of_lt (show j - 112 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 112 + (j - 112) = j by omega, h1]
  rfl

theorem batch30 : ∀ r ∈ (lateWitnessData4.toList.drop 116).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey30 : ∀ j, 116 ≤ j → j < 120 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch30
  apply List.mem_of_getElem? (i := j - 116)
  rw [List.getElem?_take_of_lt (show j - 116 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 116 + (j - 116) = j by omega, h1]
  rfl

theorem batch31 : ∀ r ∈ (lateWitnessData4.toList.drop 120).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey31 : ∀ j, 120 ≤ j → j < 124 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch31
  apply List.mem_of_getElem? (i := j - 120)
  rw [List.getElem?_take_of_lt (show j - 120 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 120 + (j - 120) = j by omega, h1]
  rfl

theorem batch32 : ∀ r ∈ (lateWitnessData4.toList.drop 124).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey32 : ∀ j, 124 ≤ j → j < 128 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch32
  apply List.mem_of_getElem? (i := j - 124)
  rw [List.getElem?_take_of_lt (show j - 124 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 124 + (j - 124) = j by omega, h1]
  rfl

theorem batch33 : ∀ r ∈ (lateWitnessData4.toList.drop 128).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey33 : ∀ j, 128 ≤ j → j < 132 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch33
  apply List.mem_of_getElem? (i := j - 128)
  rw [List.getElem?_take_of_lt (show j - 128 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 128 + (j - 128) = j by omega, h1]
  rfl

theorem batch34 : ∀ r ∈ (lateWitnessData4.toList.drop 132).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey34 : ∀ j, 132 ≤ j → j < 136 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch34
  apply List.mem_of_getElem? (i := j - 132)
  rw [List.getElem?_take_of_lt (show j - 132 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 132 + (j - 132) = j by omega, h1]
  rfl

theorem batch35 : ∀ r ∈ (lateWitnessData4.toList.drop 136).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey35 : ∀ j, 136 ≤ j → j < 140 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch35
  apply List.mem_of_getElem? (i := j - 136)
  rw [List.getElem?_take_of_lt (show j - 136 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 136 + (j - 136) = j by omega, h1]
  rfl

theorem batch36 : ∀ r ∈ (lateWitnessData4.toList.drop 140).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey36 : ∀ j, 140 ≤ j → j < 144 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch36
  apply List.mem_of_getElem? (i := j - 140)
  rw [List.getElem?_take_of_lt (show j - 140 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 140 + (j - 140) = j by omega, h1]
  rfl

theorem batch37 : ∀ r ∈ (lateWitnessData4.toList.drop 144).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey37 : ∀ j, 144 ≤ j → j < 148 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch37
  apply List.mem_of_getElem? (i := j - 144)
  rw [List.getElem?_take_of_lt (show j - 144 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 144 + (j - 144) = j by omega, h1]
  rfl

theorem batch38 : ∀ r ∈ (lateWitnessData4.toList.drop 148).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey38 : ∀ j, 148 ≤ j → j < 152 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch38
  apply List.mem_of_getElem? (i := j - 148)
  rw [List.getElem?_take_of_lt (show j - 148 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 148 + (j - 148) = j by omega, h1]
  rfl

theorem batch39 : ∀ r ∈ (lateWitnessData4.toList.drop 152).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey39 : ∀ j, 152 ≤ j → j < 156 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch39
  apply List.mem_of_getElem? (i := j - 152)
  rw [List.getElem?_take_of_lt (show j - 152 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 152 + (j - 152) = j by omega, h1]
  rfl

theorem batch40 : ∀ r ∈ (lateWitnessData4.toList.drop 156).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey40 : ∀ j, 156 ≤ j → j < 160 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch40
  apply List.mem_of_getElem? (i := j - 156)
  rw [List.getElem?_take_of_lt (show j - 156 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 156 + (j - 156) = j by omega, h1]
  rfl

theorem batch41 : ∀ r ∈ (lateWitnessData4.toList.drop 160).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey41 : ∀ j, 160 ≤ j → j < 164 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch41
  apply List.mem_of_getElem? (i := j - 160)
  rw [List.getElem?_take_of_lt (show j - 160 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 160 + (j - 160) = j by omega, h1]
  rfl

theorem batch42 : ∀ r ∈ (lateWitnessData4.toList.drop 164).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey42 : ∀ j, 164 ≤ j → j < 168 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch42
  apply List.mem_of_getElem? (i := j - 164)
  rw [List.getElem?_take_of_lt (show j - 164 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 164 + (j - 164) = j by omega, h1]
  rfl

theorem batch43 : ∀ r ∈ (lateWitnessData4.toList.drop 168).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey43 : ∀ j, 168 ≤ j → j < 172 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch43
  apply List.mem_of_getElem? (i := j - 168)
  rw [List.getElem?_take_of_lt (show j - 168 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 168 + (j - 168) = j by omega, h1]
  rfl

theorem batch44 : ∀ r ∈ (lateWitnessData4.toList.drop 172).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey44 : ∀ j, 172 ≤ j → j < 176 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch44
  apply List.mem_of_getElem? (i := j - 172)
  rw [List.getElem?_take_of_lt (show j - 172 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 172 + (j - 172) = j by omega, h1]
  rfl

theorem batch45 : ∀ r ∈ (lateWitnessData4.toList.drop 176).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey45 : ∀ j, 176 ≤ j → j < 180 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch45
  apply List.mem_of_getElem? (i := j - 176)
  rw [List.getElem?_take_of_lt (show j - 176 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 176 + (j - 176) = j by omega, h1]
  rfl

theorem batch46 : ∀ r ∈ (lateWitnessData4.toList.drop 180).take 4, fcAll r = true := by
  decide +kernel

theorem chunkKey46 : ∀ j, 180 ≤ j → j < 184 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch46
  apply List.mem_of_getElem? (i := j - 180)
  rw [List.getElem?_take_of_lt (show j - 180 < 4 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 180 + (j - 180) = j by omega, h1]
  rfl

theorem batch47 : ∀ r ∈ (lateWitnessData4.toList.drop 184).take 1, fcAll r = true := by
  decide +kernel

theorem chunkKey47 : ∀ j, 184 ≤ j → j < 185 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData4.size := by rw [sD4]; omega
  have h1 : lateWitnessData4[j]? = some (lateWitnessData4[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch47
  apply List.mem_of_getElem? (i := j - 184)
  rw [List.getElem?_take_of_lt (show j - 184 < 1 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 184 + (j - 184) = j by omega, h1]
  rfl

theorem key : ∀ j, j < 185 →
    certWitnessValid (lateWitnessOf ((lateWitnessData4[j]?).getD rdflt)) := by
  intro j hj
  rcases (show (0 ≤ j ∧ j < 4) ∨ (4 ≤ j ∧ j < 8) ∨ (8 ≤ j ∧ j < 12) ∨ (12 ≤ j ∧ j < 16) ∨ (16 ≤ j ∧ j < 20) ∨ (20 ≤ j ∧ j < 24) ∨ (24 ≤ j ∧ j < 28) ∨ (28 ≤ j ∧ j < 32) ∨ (32 ≤ j ∧ j < 36) ∨ (36 ≤ j ∧ j < 40) ∨ (40 ≤ j ∧ j < 44) ∨ (44 ≤ j ∧ j < 48) ∨ (48 ≤ j ∧ j < 52) ∨ (52 ≤ j ∧ j < 56) ∨ (56 ≤ j ∧ j < 60) ∨ (60 ≤ j ∧ j < 64) ∨ (64 ≤ j ∧ j < 68) ∨ (68 ≤ j ∧ j < 72) ∨ (72 ≤ j ∧ j < 76) ∨ (76 ≤ j ∧ j < 80) ∨ (80 ≤ j ∧ j < 84) ∨ (84 ≤ j ∧ j < 88) ∨ (88 ≤ j ∧ j < 92) ∨ (92 ≤ j ∧ j < 96) ∨ (96 ≤ j ∧ j < 100) ∨ (100 ≤ j ∧ j < 104) ∨ (104 ≤ j ∧ j < 108) ∨ (108 ≤ j ∧ j < 112) ∨ (112 ≤ j ∧ j < 116) ∨ (116 ≤ j ∧ j < 120) ∨ (120 ≤ j ∧ j < 124) ∨ (124 ≤ j ∧ j < 128) ∨ (128 ≤ j ∧ j < 132) ∨ (132 ≤ j ∧ j < 136) ∨ (136 ≤ j ∧ j < 140) ∨ (140 ≤ j ∧ j < 144) ∨ (144 ≤ j ∧ j < 148) ∨ (148 ≤ j ∧ j < 152) ∨ (152 ≤ j ∧ j < 156) ∨ (156 ≤ j ∧ j < 160) ∨ (160 ≤ j ∧ j < 164) ∨ (164 ≤ j ∧ j < 168) ∨ (168 ≤ j ∧ j < 172) ∨ (172 ≤ j ∧ j < 176) ∨ (176 ≤ j ∧ j < 180) ∨ (180 ≤ j ∧ j < 184) ∨ (184 ≤ j ∧ j < 185) by omega) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact chunkKey1 j h.1 h.2
  · exact chunkKey2 j h.1 h.2
  · exact chunkKey3 j h.1 h.2
  · exact chunkKey4 j h.1 h.2
  · exact chunkKey5 j h.1 h.2
  · exact chunkKey6 j h.1 h.2
  · exact chunkKey7 j h.1 h.2
  · exact chunkKey8 j h.1 h.2
  · exact chunkKey9 j h.1 h.2
  · exact chunkKey10 j h.1 h.2
  · exact chunkKey11 j h.1 h.2
  · exact chunkKey12 j h.1 h.2
  · exact chunkKey13 j h.1 h.2
  · exact chunkKey14 j h.1 h.2
  · exact chunkKey15 j h.1 h.2
  · exact chunkKey16 j h.1 h.2
  · exact chunkKey17 j h.1 h.2
  · exact chunkKey18 j h.1 h.2
  · exact chunkKey19 j h.1 h.2
  · exact chunkKey20 j h.1 h.2
  · exact chunkKey21 j h.1 h.2
  · exact chunkKey22 j h.1 h.2
  · exact chunkKey23 j h.1 h.2
  · exact chunkKey24 j h.1 h.2
  · exact chunkKey25 j h.1 h.2
  · exact chunkKey26 j h.1 h.2
  · exact chunkKey27 j h.1 h.2
  · exact chunkKey28 j h.1 h.2
  · exact chunkKey29 j h.1 h.2
  · exact chunkKey30 j h.1 h.2
  · exact chunkKey31 j h.1 h.2
  · exact chunkKey32 j h.1 h.2
  · exact chunkKey33 j h.1 h.2
  · exact chunkKey34 j h.1 h.2
  · exact chunkKey35 j h.1 h.2
  · exact chunkKey36 j h.1 h.2
  · exact chunkKey37 j h.1 h.2
  · exact chunkKey38 j h.1 h.2
  · exact chunkKey39 j h.1 h.2
  · exact chunkKey40 j h.1 h.2
  · exact chunkKey41 j h.1 h.2
  · exact chunkKey42 j h.1 h.2
  · exact chunkKey43 j h.1 h.2
  · exact chunkKey44 j h.1 h.2
  · exact chunkKey45 j h.1 h.2
  · exact chunkKey46 j h.1 h.2
  · exact chunkKey47 j h.1 h.2

theorem solution : lateWitnessBatch 555 740 := by
  intro i hlo hhi
  have hix := hidx i hlo hhi
  have heq : (lateCatalog.witnesses[i]?).getD rdflt = (lateWitnessData4[i - 555]?).getD rdflt := by
    rw [hix]
  rw [lateWitness_eq i _ heq]
  exact key (i - 555) (by omega)
