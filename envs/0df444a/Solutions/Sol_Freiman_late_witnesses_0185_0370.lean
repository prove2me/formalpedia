-- Prove2me | solution 1 for Freiman.late_witnesses_0185_0370
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-12T00:25:35.980361+00:00
-- url     : https://prove2.me/submissions/f38d29a5-8fa4-4ee8-98ee-121d31dd2666

import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic

set_option maxRecDepth 8000
set_option maxHeartbeats 0

open Freiman
set_option linter.all false

/- ===================================================================
   The global witness array `lateCatalog.witnesses` is the concatenation
   `lateWitnessData1 ++ ... ++ lateWitnessData8` (sizes 185x7 + 178 = 1473).
   For this leaf (global index range [185,370)) every witness lives in
   block `lateWitnessData2` alone, so we avoid ever forcing the kernel to reduce the
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

theorem hidx : ∀ i : ℕ, 185 ≤ i → i < 370 →
    lateCatalog.witnesses[i]? = lateWitnessData2[i - 185]? := by
  intro i hlo hhi
  show (lateWitnessData1 ++ lateWitnessData2 ++ lateWitnessData3 ++ lateWitnessData4 ++
    lateWitnessData5 ++ lateWitnessData6 ++ lateWitnessData7 ++ lateWitnessData8)[i]? = _
  rw [Array.getElem?_append_left (by rw [s7]; omega), Array.getElem?_append_left (by rw [s6]; omega), Array.getElem?_append_left (by rw [s5]; omega), Array.getElem?_append_left (by rw [s4]; omega), Array.getElem?_append_left (by rw [s3]; omega), Array.getElem?_append_left (by rw [s2]; omega), Array.getElem?_append_right (by rw [sD1]; omega), sD1]

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

theorem batch1 : ∀ r ∈ (lateWitnessData2.toList.drop 0).take 20, fcAll r = true := by
  decide +kernel

theorem chunkKey1 : ∀ j, 0 ≤ j → j < 20 →
    certWitnessValid (lateWitnessOf ((lateWitnessData2[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData2.size := by rw [sD2]; omega
  have h1 : lateWitnessData2[j]? = some (lateWitnessData2[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch1
  apply List.mem_of_getElem? (i := j - 0)
  rw [List.getElem?_take_of_lt (show j - 0 < 20 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 0 + (j - 0) = j by omega, h1]
  rfl

theorem batch2 : ∀ r ∈ (lateWitnessData2.toList.drop 20).take 20, fcAll r = true := by
  decide +kernel

theorem chunkKey2 : ∀ j, 20 ≤ j → j < 40 →
    certWitnessValid (lateWitnessOf ((lateWitnessData2[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData2.size := by rw [sD2]; omega
  have h1 : lateWitnessData2[j]? = some (lateWitnessData2[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch2
  apply List.mem_of_getElem? (i := j - 20)
  rw [List.getElem?_take_of_lt (show j - 20 < 20 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 20 + (j - 20) = j by omega, h1]
  rfl

theorem batch3 : ∀ r ∈ (lateWitnessData2.toList.drop 40).take 20, fcAll r = true := by
  decide +kernel

theorem chunkKey3 : ∀ j, 40 ≤ j → j < 60 →
    certWitnessValid (lateWitnessOf ((lateWitnessData2[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData2.size := by rw [sD2]; omega
  have h1 : lateWitnessData2[j]? = some (lateWitnessData2[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch3
  apply List.mem_of_getElem? (i := j - 40)
  rw [List.getElem?_take_of_lt (show j - 40 < 20 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 40 + (j - 40) = j by omega, h1]
  rfl

theorem batch4 : ∀ r ∈ (lateWitnessData2.toList.drop 60).take 20, fcAll r = true := by
  decide +kernel

theorem chunkKey4 : ∀ j, 60 ≤ j → j < 80 →
    certWitnessValid (lateWitnessOf ((lateWitnessData2[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData2.size := by rw [sD2]; omega
  have h1 : lateWitnessData2[j]? = some (lateWitnessData2[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch4
  apply List.mem_of_getElem? (i := j - 60)
  rw [List.getElem?_take_of_lt (show j - 60 < 20 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 60 + (j - 60) = j by omega, h1]
  rfl

theorem batch5 : ∀ r ∈ (lateWitnessData2.toList.drop 80).take 20, fcAll r = true := by
  decide +kernel

theorem chunkKey5 : ∀ j, 80 ≤ j → j < 100 →
    certWitnessValid (lateWitnessOf ((lateWitnessData2[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData2.size := by rw [sD2]; omega
  have h1 : lateWitnessData2[j]? = some (lateWitnessData2[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch5
  apply List.mem_of_getElem? (i := j - 80)
  rw [List.getElem?_take_of_lt (show j - 80 < 20 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 80 + (j - 80) = j by omega, h1]
  rfl

theorem batch6 : ∀ r ∈ (lateWitnessData2.toList.drop 100).take 20, fcAll r = true := by
  decide +kernel

theorem chunkKey6 : ∀ j, 100 ≤ j → j < 120 →
    certWitnessValid (lateWitnessOf ((lateWitnessData2[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData2.size := by rw [sD2]; omega
  have h1 : lateWitnessData2[j]? = some (lateWitnessData2[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch6
  apply List.mem_of_getElem? (i := j - 100)
  rw [List.getElem?_take_of_lt (show j - 100 < 20 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 100 + (j - 100) = j by omega, h1]
  rfl

theorem batch7 : ∀ r ∈ (lateWitnessData2.toList.drop 120).take 20, fcAll r = true := by
  decide +kernel

theorem chunkKey7 : ∀ j, 120 ≤ j → j < 140 →
    certWitnessValid (lateWitnessOf ((lateWitnessData2[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData2.size := by rw [sD2]; omega
  have h1 : lateWitnessData2[j]? = some (lateWitnessData2[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch7
  apply List.mem_of_getElem? (i := j - 120)
  rw [List.getElem?_take_of_lt (show j - 120 < 20 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 120 + (j - 120) = j by omega, h1]
  rfl

theorem batch8 : ∀ r ∈ (lateWitnessData2.toList.drop 140).take 20, fcAll r = true := by
  decide +kernel

theorem chunkKey8 : ∀ j, 140 ≤ j → j < 160 →
    certWitnessValid (lateWitnessOf ((lateWitnessData2[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData2.size := by rw [sD2]; omega
  have h1 : lateWitnessData2[j]? = some (lateWitnessData2[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch8
  apply List.mem_of_getElem? (i := j - 140)
  rw [List.getElem?_take_of_lt (show j - 140 < 20 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 140 + (j - 140) = j by omega, h1]
  rfl

theorem batch9 : ∀ r ∈ (lateWitnessData2.toList.drop 160).take 20, fcAll r = true := by
  decide +kernel

theorem chunkKey9 : ∀ j, 160 ≤ j → j < 180 →
    certWitnessValid (lateWitnessOf ((lateWitnessData2[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData2.size := by rw [sD2]; omega
  have h1 : lateWitnessData2[j]? = some (lateWitnessData2[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch9
  apply List.mem_of_getElem? (i := j - 160)
  rw [List.getElem?_take_of_lt (show j - 160 < 20 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 160 + (j - 160) = j by omega, h1]
  rfl

theorem batch10 : ∀ r ∈ (lateWitnessData2.toList.drop 180).take 5, fcAll r = true := by
  decide +kernel

theorem chunkKey10 : ∀ j, 180 ≤ j → j < 185 →
    certWitnessValid (lateWitnessOf ((lateWitnessData2[j]?).getD rdflt)) := by
  intro j hj1 hj2
  apply fcAll_imp
  have hbound : j < lateWitnessData2.size := by rw [sD2]; omega
  have h1 : lateWitnessData2[j]? = some (lateWitnessData2[j]'hbound) := Array.getElem?_eq_getElem hbound
  apply batch10
  apply List.mem_of_getElem? (i := j - 180)
  rw [List.getElem?_take_of_lt (show j - 180 < 5 by omega), List.getElem?_drop,
      Array.getElem?_toList, show 180 + (j - 180) = j by omega, h1]
  rfl

theorem key : ∀ j, j < 185 →
    certWitnessValid (lateWitnessOf ((lateWitnessData2[j]?).getD rdflt)) := by
  intro j hj
  rcases (show (0 ≤ j ∧ j < 20) ∨ (20 ≤ j ∧ j < 40) ∨ (40 ≤ j ∧ j < 60) ∨ (60 ≤ j ∧ j < 80) ∨ (80 ≤ j ∧ j < 100) ∨ (100 ≤ j ∧ j < 120) ∨ (120 ≤ j ∧ j < 140) ∨ (140 ≤ j ∧ j < 160) ∨ (160 ≤ j ∧ j < 180) ∨ (180 ≤ j ∧ j < 185) by omega) with h | h | h | h | h | h | h | h | h | h
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

theorem solution : lateWitnessBatch 185 370 := by
  intro i hlo hhi
  have hix := hidx i hlo hhi
  have heq : (lateCatalog.witnesses[i]?).getD rdflt = (lateWitnessData2[i - 185]?).getD rdflt := by
    rw [hix]
  rw [lateWitness_eq i _ heq]
  exact key (i - 185) (by omega)
