-- Prove2me | solution 2 for Freiman.lowerHistory_witnesses_1000_1100
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-11T21:56:08.776265+00:00
-- url     : https://prove2.me/submissions/cb601c22-9c60-470c-9fb5-5c0514c5eb32

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic

open Freiman
set_option linter.all false
set_option maxRecDepth 4000000
set_option maxHeartbeats 4000000

/- ===================================================================
   PART 1: fast bound lookup, avoiding the O(n) six-way array
   concatenation `lowerHistoryBounds = B01 ++ ... ++ B06` that the
   kernel would otherwise re-walk for every single bound reference.
   =================================================================== -/

abbrev bdflt : CertBound := ⟨true,false,⟨⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩⟩⟩

def fastBound? (n : ℕ) : Option CertBound :=
  if n - 1 < 200 then lowerHistoryBounds01[n-1]? else
  if n - 1 < 400 then lowerHistoryBounds02[n-1-200]? else
  if n - 1 < 600 then lowerHistoryBounds03[n-1-400]? else
  if n - 1 < 800 then lowerHistoryBounds04[n-1-600]? else
  if n - 1 < 1000 then lowerHistoryBounds05[n-1-800]? else lowerHistoryBounds06[n-1-1000]?
def fastBound (n : ℕ) : CertBound := (fastBound? n).getD bdflt

theorem sB1 : lowerHistoryBounds01.size = 200 := by decide
theorem sB2 : lowerHistoryBounds02.size = 200 := by decide
theorem sB3 : lowerHistoryBounds03.size = 200 := by decide
theorem sB4 : lowerHistoryBounds04.size = 200 := by decide
theorem sB5 : lowerHistoryBounds05.size = 200 := by decide
theorem s12 : (lowerHistoryBounds01 ++ lowerHistoryBounds02).size = 400 := by
  rw [Array.size_append, sB1, sB2]
theorem s13 : (lowerHistoryBounds01 ++ lowerHistoryBounds02 ++ lowerHistoryBounds03).size = 600 := by
  rw [Array.size_append, s12, sB3]
theorem s14 : (lowerHistoryBounds01 ++ lowerHistoryBounds02 ++ lowerHistoryBounds03 ++ lowerHistoryBounds04).size = 800 := by
  rw [Array.size_append, s13, sB4]
theorem s15 : (lowerHistoryBounds01 ++ lowerHistoryBounds02 ++ lowerHistoryBounds03 ++ lowerHistoryBounds04 ++ lowerHistoryBounds05).size = 1000 := by
  rw [Array.size_append, s14, sB5]

theorem bound_eq? (n : ℕ) : lowerHistoryBounds[n-1]? = fastBound? n := by
  unfold fastBound? lowerHistoryBounds
  rcases (show n - 1 < 200 ∨ (¬ n - 1 < 200 ∧ n - 1 < 400) ∨ (¬ n - 1 < 200 ∧ ¬ n - 1 < 400 ∧ n - 1 < 600) ∨
    (¬ n - 1 < 200 ∧ ¬ n - 1 < 400 ∧ ¬ n - 1 < 600 ∧ n - 1 < 800) ∨
    (¬ n - 1 < 200 ∧ ¬ n - 1 < 400 ∧ ¬ n - 1 < 600 ∧ ¬ n - 1 < 800 ∧ n - 1 < 1000) ∨
    (¬ n - 1 < 200 ∧ ¬ n - 1 < 400 ∧ ¬ n - 1 < 600 ∧ ¬ n - 1 < 800 ∧ ¬ n - 1 < 1000) by omega) with
    h1 | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4, h5⟩
  · rw [if_pos h1, Array.getElem?_append_left (by rw [s15]; omega), Array.getElem?_append_left (by rw [s14]; omega), Array.getElem?_append_left (by rw [s13]; omega), Array.getElem?_append_left (by rw [s12]; omega), Array.getElem?_append_left (by rw [sB1]; omega)]
  · rw [if_neg h1, if_pos h2, Array.getElem?_append_left (by rw [s15]; omega), Array.getElem?_append_left (by rw [s14]; omega), Array.getElem?_append_left (by rw [s13]; omega), Array.getElem?_append_left (by rw [s12]; omega), Array.getElem?_append_right (by rw [sB1]; omega), sB1]
  · rw [if_neg h1, if_neg h2, if_pos h3, Array.getElem?_append_left (by rw [s15]; omega), Array.getElem?_append_left (by rw [s14]; omega), Array.getElem?_append_left (by rw [s13]; omega), Array.getElem?_append_right (by rw [s12]; omega), s12]
  · rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4, Array.getElem?_append_left (by rw [s15]; omega), Array.getElem?_append_left (by rw [s14]; omega), Array.getElem?_append_right (by rw [s13]; omega), s13]
  · rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5, Array.getElem?_append_left (by rw [s15]; omega), Array.getElem?_append_right (by rw [s14]; omega), s14]
  · rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, Array.getElem?_append_right (by rw [s15]; omega), s15]

theorem bound_eq (n : ℕ) : lowerHistoryBound n = fastBound n := by
  unfold lowerHistoryBound fastBound; rw [bound_eq?]

theorem hfun : lowerHistoryBound = fastBound := funext bound_eq

/- ===================================================================
   PART 2: mirrored, Bool-valued, pointwise version of `certWitnessValid`.
   =================================================================== -/

abbrev wdflt : CertWitness :=
  ⟨lowerHistoryBound 0, lowerHistoryBound 0, ⟨0,1,0,1⟩, fun _ _ => ⟨0,0,0,0⟩, fun _ _ => 0⟩

def fcRect (R : CertRectangle) : Bool :=
  decide (R.r0 < R.r1) && decide (R.s0 < R.s1) && decide (0 ≤ R.r0)
def fcThr (t : CertThreshold) : Bool :=
  decide (0 ≤ certFieldLower t.x0) && decide (0 ≤ certFieldLower t.x1)
def fcCoef (C D : CertPoly22) : Bool :=
  decide (C 0 0 = D 0 0) && decide (C 0 1 = D 0 1) && decide (C 0 2 = D 0 2) &&
  decide (C 1 0 = D 1 0) && decide (C 1 1 = D 1 1) && decide (C 1 2 = D 1 2) &&
  decide (C 2 0 = D 2 0) && decide (C 2 1 = D 2 1) && decide (C 2 2 = D 2 2)
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
def fcCoefW (w : CertWitness) : Bool :=
  fcCoef w.coefficients (certBernsteinCoefficients
    (certCrossPolynomial w.lowerBound.threshold w.upperBound.threshold) w.rectangle)

theorem fcRect_imp {R : CertRectangle} (h : fcRect R = true) :
    certRectangleValid R ∧ 0 ≤ R.r0 := by
  unfold fcRect at h; unfold certRectangleValid
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨⟨h.1.1, h.1.2⟩, h.2⟩

theorem fcThr_imp {t : CertThreshold} (h : fcThr t = true) : certThresholdDataValid t := by
  unfold fcThr at h; unfold certThresholdDataValid
  simpa using h

theorem fcCoef_imp {C D : CertPoly22} (h : fcCoef C D = true) : C = D := by
  unfold fcCoef at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  funext i j
  fin_cases i <;> fin_cases j <;> simp_all

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

theorem fastCheck_imp {w : CertWitness} (h1 : fcRest w = true) (h2 : fcCoefW w = true)
    (h3 : fcCBVs w.coefficients w.lowerBounds = true) : certWitnessValid w := by
  obtain ⟨e1,e2,e3,e4,e5,e6,e7⟩ := fcRest_imp h1
  refine ⟨e1,e2,e3,e4,e5,e6, fcCoef_imp h2, fcCBVs_imp h3, e7⟩

theorem chunk_mem {s n j : ℕ} (h1 : s ≤ j) (h2 : j < s + n) : j ∈ List.range' s n :=
  List.mem_range'_1.mpr ⟨h1, h2⟩

/- ===================================================================
   PART 2b: fast witness-array lookup, avoiding the O(n) six-way array
   concatenation `lowerHistoryWitnesses = W01 ++ ... ++ W06`.
   =================================================================== -/

def fastWitness? (n : ℕ) : Option CertWitness :=
  if n < 200 then lowerHistoryWitnesses01[n]? else
  if n < 400 then lowerHistoryWitnesses02[n-200]? else
  if n < 600 then lowerHistoryWitnesses03[n-400]? else
  if n < 800 then lowerHistoryWitnesses04[n-600]? else
  if n < 1000 then lowerHistoryWitnesses05[n-800]? else lowerHistoryWitnesses06[n-1000]?

theorem wB1 : lowerHistoryWitnesses01.size = 200 := by decide
theorem wB2 : lowerHistoryWitnesses02.size = 200 := by decide
theorem wB3 : lowerHistoryWitnesses03.size = 200 := by decide
theorem wB4 : lowerHistoryWitnesses04.size = 200 := by decide
theorem wB5 : lowerHistoryWitnesses05.size = 200 := by decide
theorem w12 : (lowerHistoryWitnesses01 ++ lowerHistoryWitnesses02).size = 400 := by
  rw [Array.size_append, wB1, wB2]
theorem w13 : (lowerHistoryWitnesses01 ++ lowerHistoryWitnesses02 ++ lowerHistoryWitnesses03).size = 600 := by
  rw [Array.size_append, w12, wB3]
theorem w14 : (lowerHistoryWitnesses01 ++ lowerHistoryWitnesses02 ++ lowerHistoryWitnesses03 ++ lowerHistoryWitnesses04).size = 800 := by
  rw [Array.size_append, w13, wB4]
theorem w15 : (lowerHistoryWitnesses01 ++ lowerHistoryWitnesses02 ++ lowerHistoryWitnesses03 ++ lowerHistoryWitnesses04 ++ lowerHistoryWitnesses05).size = 1000 := by
  rw [Array.size_append, w14, wB5]

theorem windex? (n : ℕ) : lowerHistoryWitnesses[n]? = fastWitness? n := by
  unfold fastWitness? lowerHistoryWitnesses
  rcases (show n < 200 ∨ (¬ n < 200 ∧ n < 400) ∨ (¬ n < 200 ∧ ¬ n < 400 ∧ n < 600) ∨
    (¬ n < 200 ∧ ¬ n < 400 ∧ ¬ n < 600 ∧ n < 800) ∨
    (¬ n < 200 ∧ ¬ n < 400 ∧ ¬ n < 600 ∧ ¬ n < 800 ∧ n < 1000) ∨
    (¬ n < 200 ∧ ¬ n < 400 ∧ ¬ n < 600 ∧ ¬ n < 800 ∧ ¬ n < 1000) by omega) with
    h1 | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4, h5⟩
  · rw [if_pos h1, Array.getElem?_append_left (by rw [w15]; omega), Array.getElem?_append_left (by rw [w14]; omega), Array.getElem?_append_left (by rw [w13]; omega), Array.getElem?_append_left (by rw [w12]; omega), Array.getElem?_append_left (by rw [wB1]; omega)]
  · rw [if_neg h1, if_pos h2, Array.getElem?_append_left (by rw [w15]; omega), Array.getElem?_append_left (by rw [w14]; omega), Array.getElem?_append_left (by rw [w13]; omega), Array.getElem?_append_left (by rw [w12]; omega), Array.getElem?_append_right (by rw [wB1]; omega), wB1]
  · rw [if_neg h1, if_neg h2, if_pos h3, Array.getElem?_append_left (by rw [w15]; omega), Array.getElem?_append_left (by rw [w14]; omega), Array.getElem?_append_left (by rw [w13]; omega), Array.getElem?_append_right (by rw [w12]; omega), w12]
  · rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4, Array.getElem?_append_left (by rw [w15]; omega), Array.getElem?_append_left (by rw [w14]; omega), Array.getElem?_append_right (by rw [w13]; omega), w13]
  · rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5, Array.getElem?_append_left (by rw [w15]; omega), Array.getElem?_append_right (by rw [w14]; omega), w14]
  · rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, Array.getElem?_append_right (by rw [w15]; omega), w15]


/- ===================================================================
   PART 3: range-specific index fact -- for i in [1000,1100) the global
   witness index always resolves to block 06 (lowerHistoryWitnesses06) alone,
   since the range never straddles a block boundary.
   =================================================================== -/

theorem hidx : ∀ i : ℕ, 1000 ≤ i → i < 1100 →
    lowerHistoryWitnesses[i]? = lowerHistoryWitnesses06[i - 1000]? := by
  intro i _ _
  rw [windex?]
  unfold fastWitness?
  rw [if_neg (show ¬ (i < 200) by omega), if_neg (show ¬ (i < 400) by omega), if_neg (show ¬ (i < 600) by omega), if_neg (show ¬ (i < 800) by omega), if_neg (show ¬ (i < 1000) by omega)]
  all_goals simp

theorem batchA1 : ∀ j ∈ List.range' 0 20,
    fcRest ((lowerHistoryWitnesses06[j]?).getD wdflt) = true := by
  delta lowerHistoryWitnesses06; rw [hfun]; decide +kernel

theorem batchA2 : ∀ j ∈ List.range' 20 20,
    fcRest ((lowerHistoryWitnesses06[j]?).getD wdflt) = true := by
  delta lowerHistoryWitnesses06; rw [hfun]; decide +kernel

theorem batchA3 : ∀ j ∈ List.range' 40 20,
    fcRest ((lowerHistoryWitnesses06[j]?).getD wdflt) = true := by
  delta lowerHistoryWitnesses06; rw [hfun]; decide +kernel

theorem batchA4 : ∀ j ∈ List.range' 60 20,
    fcRest ((lowerHistoryWitnesses06[j]?).getD wdflt) = true := by
  delta lowerHistoryWitnesses06; rw [hfun]; decide +kernel

theorem batchA5 : ∀ j ∈ List.range' 80 20,
    fcRest ((lowerHistoryWitnesses06[j]?).getD wdflt) = true := by
  delta lowerHistoryWitnesses06; rw [hfun]; decide +kernel

theorem batchB1 : ∀ j ∈ List.range' 0 20,
    fcCoefW ((lowerHistoryWitnesses06[j]?).getD wdflt) = true := by
  delta lowerHistoryWitnesses06; rw [hfun]; decide +kernel

theorem batchB2 : ∀ j ∈ List.range' 20 20,
    fcCoefW ((lowerHistoryWitnesses06[j]?).getD wdflt) = true := by
  delta lowerHistoryWitnesses06; rw [hfun]; decide +kernel

theorem batchB3 : ∀ j ∈ List.range' 40 20,
    fcCoefW ((lowerHistoryWitnesses06[j]?).getD wdflt) = true := by
  delta lowerHistoryWitnesses06; rw [hfun]; decide +kernel

theorem batchB4 : ∀ j ∈ List.range' 60 20,
    fcCoefW ((lowerHistoryWitnesses06[j]?).getD wdflt) = true := by
  delta lowerHistoryWitnesses06; rw [hfun]; decide +kernel

theorem batchB5 : ∀ j ∈ List.range' 80 20,
    fcCoefW ((lowerHistoryWitnesses06[j]?).getD wdflt) = true := by
  delta lowerHistoryWitnesses06; rw [hfun]; decide +kernel

theorem batchC1 : ∀ j ∈ List.range' 0 20,
    fcCBVs ((lowerHistoryWitnesses06[j]?).getD wdflt).coefficients
      ((lowerHistoryWitnesses06[j]?).getD wdflt).lowerBounds = true := by
  decide +kernel

theorem batchC2 : ∀ j ∈ List.range' 20 20,
    fcCBVs ((lowerHistoryWitnesses06[j]?).getD wdflt).coefficients
      ((lowerHistoryWitnesses06[j]?).getD wdflt).lowerBounds = true := by
  decide +kernel

theorem batchC3 : ∀ j ∈ List.range' 40 20,
    fcCBVs ((lowerHistoryWitnesses06[j]?).getD wdflt).coefficients
      ((lowerHistoryWitnesses06[j]?).getD wdflt).lowerBounds = true := by
  decide +kernel

theorem batchC4 : ∀ j ∈ List.range' 60 20,
    fcCBVs ((lowerHistoryWitnesses06[j]?).getD wdflt).coefficients
      ((lowerHistoryWitnesses06[j]?).getD wdflt).lowerBounds = true := by
  decide +kernel

theorem batchC5 : ∀ j ∈ List.range' 80 20,
    fcCBVs ((lowerHistoryWitnesses06[j]?).getD wdflt).coefficients
      ((lowerHistoryWitnesses06[j]?).getD wdflt).lowerBounds = true := by
  decide +kernel

theorem key : ∀ j ∈ List.range' 0 100,
    certWitnessValid ((lowerHistoryWitnesses06[j]?).getD wdflt) := by
  intro j hj
  simp only [List.mem_range'_1] at hj
  rcases (show
      (0 ≤ j ∧ j < 20) ∨
      (20 ≤ j ∧ j < 40) ∨
      (40 ≤ j ∧ j < 60) ∨
      (60 ≤ j ∧ j < 80) ∨
      (80 ≤ j ∧ j < 100)
      by omega) with
      h | h | h | h | h
  · exact fastCheck_imp (batchA1 j (chunk_mem h.1 h.2)) (batchB1 j (chunk_mem h.1 h.2))
      (batchC1 j (chunk_mem h.1 h.2))
  · exact fastCheck_imp (batchA2 j (chunk_mem h.1 h.2)) (batchB2 j (chunk_mem h.1 h.2))
      (batchC2 j (chunk_mem h.1 h.2))
  · exact fastCheck_imp (batchA3 j (chunk_mem h.1 h.2)) (batchB3 j (chunk_mem h.1 h.2))
      (batchC3 j (chunk_mem h.1 h.2))
  · exact fastCheck_imp (batchA4 j (chunk_mem h.1 h.2)) (batchB4 j (chunk_mem h.1 h.2))
      (batchC4 j (chunk_mem h.1 h.2))
  · exact fastCheck_imp (batchA5 j (chunk_mem h.1 h.2)) (batchB5 j (chunk_mem h.1 h.2))
      (batchC5 j (chunk_mem h.1 h.2))

theorem solution : lowerHistoryWitnessBatch 1000 1100 := by
  intro i hlo hhi
  have hk := key (i - 1000) (chunk_mem (by omega) (by omega))
  show certWitnessValid ((lowerHistoryWitnesses[i + 1 - 1]?).getD _)
  rw [Nat.add_sub_cancel, hidx i hlo hhi]
  exact hk
