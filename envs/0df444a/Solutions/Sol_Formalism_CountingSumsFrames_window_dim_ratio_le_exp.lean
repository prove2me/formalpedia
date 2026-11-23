-- Prove2me | solution 1 for Formalism.CountingSumsFrames.window_dim_ratio_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:57:57.360618+00:00
-- url     : https://prove2.me/submissions/3804194e-42fd-4995-8c1d-37905b896b83

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentTopRoomPublished
import Theorems.Thm_Formalism_CountingSumsFrames_binomial_ratio_exp_bound

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
theorem _root_.solution (r C C' : ℕ) (lo hi c : ℝ) (hlo : 0 < lo) (hc : 0 ≤ c)
    (h : (r : ℝ) * (hi - lo) ≤ c * lo) (h1 : lo ≤ C) (h2 : lo ≤ C') (h3 : (C : ℝ) ≤ hi)
    (h4 : (C' : ℝ) ≤ hi) :
    (r : ℝ) * |(C' : ℝ) - C| / min (C : ℝ) C' ≤ c ∧
      (dimPol r C' : ℝ) ≤ Real.exp c * dimPol r C := by
  have hmin : lo ≤ min (C : ℝ) C' := le_min h1 h2
  have habs : |(C' : ℝ) - C| ≤ hi - lo := by rw [abs_le]; constructor <;> linarith
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  constructor
  · rw [div_le_iff₀ (by linarith)]
    calc (r : ℝ) * |(C' : ℝ) - C| ≤ (r : ℝ) * (hi - lo) := by gcongr
      _ ≤ c * lo := h
      _ ≤ c * min (C : ℝ) C' := by gcongr
  · rcases le_total C C' with hle | hle
    · have hC0 : (0 : ℝ) < C := by linarith
      have hC1 : 1 ≤ C := by exact_mod_cast hC0
      refine (binomial_ratio_exp_bound r C C' hC1 hle).trans ?_
      have harg : (r : ℝ) * ((C' : ℝ) - C) / C ≤ c := by
        rw [div_le_iff₀ hC0]
        calc (r : ℝ) * ((C' : ℝ) - C) ≤ (r : ℝ) * (hi - lo) := by gcongr
          _ ≤ c * lo := h
          _ ≤ c * C := by gcongr
      gcongr
    · have hm : dimPol r C' ≤ dimPol r C := Nat.choose_le_choose r (by omega)
      have hm' : (dimPol r C' : ℝ) ≤ dimPol r C := by exact_mod_cast hm
      have he : 1 ≤ Real.exp c := Real.one_le_exp hc
      have hD0 : (0 : ℝ) ≤ dimPol r C := Nat.cast_nonneg _
      calc (dimPol r C' : ℝ) ≤ 1 * dimPol r C := by linarith
        _ ≤ Real.exp c * dimPol r C := by gcongr
end Formalism.CountingSumsFrames
