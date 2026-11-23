-- Prove2me | solution 1 for Formalism.CountingSumsFrames.binomial_ratio_exp_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:10.58148+00:00
-- url     : https://prove2.me/submissions/b942c524-8bde-4347-a20c-4af83cb5e43c

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentTopRoomPublished
import Theorems.Thm_Formalism_CountingSumsFrames_dimPol_ratio_le_pow

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
theorem _root_.solution : BinomRatioExp := by
  intro r x x' hx hxx
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hE : (x' : ℝ) ≤ Real.exp (((x' : ℝ) - x) / x) * x := by
    have h1 := Real.add_one_le_exp (((x' : ℝ) - x) / x)
    have h2 : (((x' : ℝ) - x) / x + 1) * x = x' := by field_simp; ring
    calc (x' : ℝ) = (((x' : ℝ) - x) / x + 1) * x := h2.symm
      _ ≤ Real.exp (((x' : ℝ) - x) / x) * x := by gcongr
  have h := dimPol_ratio_le_pow r x x' _ hx hxx hE
  rw [← Real.exp_nat_mul] at h
  have e : (r : ℝ) * (((x' : ℝ) - x) / x) = (r : ℝ) * ((x' : ℝ) - x) / x := by ring
  rwa [e] at h
end Formalism.CountingSumsFrames
