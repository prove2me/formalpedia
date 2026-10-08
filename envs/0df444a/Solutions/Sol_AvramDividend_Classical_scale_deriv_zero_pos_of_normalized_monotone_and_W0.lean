-- Prove2me | solution 1 for AvramDividend.Classical.scale_deriv_zero_pos_of_normalized_monotone_and_W0
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T18:16:55.448322+00:00
-- url     : https://prove2.me/submissions/8fbf1b56-b2ae-42a6-8571-c3ae73ba76ef

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_normalized_derivative_lower_bound

open AvramDividend.Classical Filter
open scoped Topology ENNReal

theorem solution (W : ℝ → ℝ) (φ : ℝ)
    (hφ : 0 < φ) (hW0 : 0 < W 0)
    (hmonoW : MonotoneOn W (Set.Ici 0))
    (htilt : MonotoneOn
      (fun t : ℝ => Real.exp (-φ * t) * W t) (Set.Ioi 0))
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x) :
    (0 : EReal) < derivZeroPlus W := by
  have hbound : ∀ x : ℝ, 0 < x →
      φ * W 0 ≤ deriv W x := by
    intro x hx
    have hWx : W 0 ≤ W x :=
      hmonoW (Set.mem_Ici.mpr (le_refl (0 : ℝ)))
        (Set.mem_Ici.mpr hx.le) hx.le
    have hd : φ * W x ≤ deriv W x :=
      normalized_derivative_lower_bound φ x htilt hx (hdiff x hx)
    exact (mul_le_mul_of_nonneg_left hWx hφ.le).trans hd
  have hlim : ((φ * W 0 : ℝ) : EReal) ≤ derivZeroPlus W := by
    unfold derivZeroPlus
    refine Filter.le_liminf_of_le (by isBoundedDefault) ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact_mod_cast hbound x (Set.mem_Ioi.mp hx)
  have hp : (0 : EReal) < ((φ * W 0 : ℝ) : EReal) := by
    exact_mod_cast mul_pos hφ hW0
  exact hp.trans_le hlim
