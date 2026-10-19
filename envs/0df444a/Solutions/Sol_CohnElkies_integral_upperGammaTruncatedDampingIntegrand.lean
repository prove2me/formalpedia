-- Prove2me | solution 1 for CohnElkies.integral_upperGammaTruncatedDampingIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/96188756-f37f-4dd8-9d46-cf2006018e69

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperCosLaplaceKernel_integrable
import Theorems.Thm_CohnElkies_integral_upperCosLaplaceKernel
import Theorems.Thm_CohnElkies_upperGammaTruncatedDampingIntegrand_eq_sum
import Theorems.Thm_CohnElkies_upperGammaLaplaceRate_pos

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η)
    (T : ℝ) (n : ℕ) :
    (∫ a : ℝ in Ioi 0,
      upperGammaTruncatedDampingIntegrand ℓ η T n a) =
      ∑ k ∈ Finset.range (n + 1),
        Real.log
          (‖((η + 2 * (k : ℝ) / ℓ : ℝ) : ℂ) +
                Complex.I * (T : ℂ)‖ /
            (η + 2 * (k : ℝ) / ℓ)) := by
  classical
  calc
    (∫ a : ℝ in Ioi 0,
      upperGammaTruncatedDampingIntegrand ℓ η T n a) =
        ∫ a : ℝ in Ioi 0,
          ∑ k ∈ Finset.range (n + 1),
            upperCosLaplaceKernel
              (η + 2 * (k : ℝ) / ℓ) T a := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro a ha
      exact upperGammaTruncatedDampingIntegrand_eq_sum
        ℓ η T n a
    _ = ∑ k ∈ Finset.range (n + 1),
          ∫ a : ℝ in Ioi 0,
            upperCosLaplaceKernel
              (η + 2 * (k : ℝ) / ℓ) T a := by
      apply integral_finsetSum
      intro k hk
      exact upperCosLaplaceKernel_integrable
        (upperGammaLaplaceRate_pos hℓ hη k) T
    _ = ∑ k ∈ Finset.range (n + 1),
        Real.log
          (‖((η + 2 * (k : ℝ) / ℓ : ℝ) : ℂ) +
                Complex.I * (T : ℂ)‖ /
            (η + 2 * (k : ℝ) / ℓ)) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact integral_upperCosLaplaceKernel
        (upperGammaLaplaceRate_pos hℓ hη k) T
end CohnElkies
