-- Prove2me | solution 1 for AvramDividend.Classical.scaleDeriv_pos_of_W0_tilted_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T20:23:12.852981+00:00
-- url     : https://prove2.me/submissions/63f3b876-44d0-4ad8-8d6d-546df3cf9394

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scale_deriv_zero_pos_of_normalized_monotone_and_W0
import Theorems.Thm_AvramDividend_Classical_scale_deriv_pos_of_normalized_monotone

open AvramDividend.Classical
open scoped Topology ENNReal

theorem solution (W : ℝ → ℝ) (φ : ℝ)
    (hφ : 0 < φ) (hW0 : 0 < W 0)
    (hmonoW : MonotoneOn W (Set.Ici 0))
    (htilt : MonotoneOn
      (fun t : ℝ => Real.exp (-φ * t) * W t) (Set.Ioi 0))
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x) :
    ∀ x : ℝ, 0 ≤ x → (0 : EReal) < scaleDeriv W x := by
  have hpositive : ∀ x : ℝ, 0 < x → 0 < W x := by
    intro x hx
    have hge : W 0 ≤ W x :=
      hmonoW (Set.mem_Ici.mpr (le_refl (0 : ℝ)))
        (Set.mem_Ici.mpr hx.le) hx.le
    exact lt_of_lt_of_le hW0 hge
  have hzero : (0 : EReal) < derivZeroPlus W :=
    scale_deriv_zero_pos_of_normalized_monotone_and_W0
      W φ hφ hW0 hmonoW htilt hdiff
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    simpa [scaleDeriv] using hzero
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have hderiv : 0 < deriv W x :=
      scale_deriv_pos_of_normalized_monotone
        W φ hφ hpositive htilt hdiff x hxpos
    have hcoe : (0 : EReal) < ((deriv W x : ℝ) : EReal) := by
      exact_mod_cast hderiv
    simpa [scaleDeriv, hx0] using hcoe
