-- Prove2me | solution 1 for Formalism.CountingSumsFrames.dimPol_ratio_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:51:39.656262+00:00
-- url     : https://prove2.me/submissions/9b2999ae-7c76-4a71-a1e8-52629d5d8312

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentTopRoomPublished
import Theorems.Thm_Formalism_CountingSumsFrames_dimPol_succ_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution (r x x' : ℕ) (E : ℝ) (hx : 1 ≤ x) (hxx : x ≤ x') (hE : (x' : ℝ) ≤ E * x) :
    (dimPol r x' : ℝ) ≤ E ^ r * dimPol r x := by
  have hx0 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hxx' : (x : ℝ) ≤ x' := by exact_mod_cast hxx
  have hE1 : 1 ≤ E := by
    by_contra hcon
    have hcon' : E < 1 := not_le.mp hcon
    nlinarith
  induction r with
  | zero => simp [dimPol]
  | succ r ih =>
    have h1 := dimPol_succ_mul r x
    have h2 := dimPol_succ_mul r x'
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
    have hr : 0 < (r : ℝ) + 1 := by linarith
    have hfac : (x' : ℝ) + r + 1 ≤ E * ((x : ℝ) + r + 1) := by nlinarith
    have hD0 : (0 : ℝ) ≤ dimPol r x' := Nat.cast_nonneg _
    have hmain : ((r : ℝ) + 1) * dimPol (r + 1) x' ≤ ((r : ℝ) + 1) * (E ^ (r + 1) * dimPol (r + 1) x) := by
      calc ((r : ℝ) + 1) * dimPol (r + 1) x' = ((x' : ℝ) + r + 1) * dimPol r x' := h2
        _ ≤ (E * ((x : ℝ) + r + 1)) * (E ^ r * dimPol r x) :=
            mul_le_mul hfac ih hD0 (by positivity)
        _ = E ^ (r + 1) * (((x : ℝ) + r + 1) * dimPol r x) := by ring
        _ = E ^ (r + 1) * (((r : ℝ) + 1) * dimPol (r + 1) x) := by rw [h1]
        _ = ((r : ℝ) + 1) * (E ^ (r + 1) * dimPol (r + 1) x) := by ring
    exact le_of_mul_le_mul_left hmain hr
end Formalism.CountingSumsFrames
