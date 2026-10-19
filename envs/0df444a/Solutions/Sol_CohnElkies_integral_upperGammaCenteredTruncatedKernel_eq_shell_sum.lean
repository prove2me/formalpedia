-- Prove2me | solution 1 for CohnElkies.integral_upperGammaCenteredTruncatedKernel_eq_shell_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/6714ee48-8183-446c-910e-9ad8c5704260

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperGammaLaplaceRate_pos
import Theorems.Thm_CohnElkies_upperCenteredLaplaceKernel_integrable
import Theorems.Thm_CohnElkies_upperGammaCenteredTruncatedKernel_eq_sum

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
      upperGammaCenteredTruncatedKernel ℓ η T n a) =
      ∑ k ∈ Finset.range (n + 1),
        (∫ a : ℝ in Ioi 0,
          upperCenteredLaplaceKernel
            (η + 2 * (k : ℝ) / ℓ) T a) := by
  classical
  calc
    (∫ a : ℝ in Ioi 0,
      upperGammaCenteredTruncatedKernel ℓ η T n a) =
        ∫ a : ℝ in Ioi 0,
          ∑ k ∈ Finset.range (n + 1),
            upperCenteredLaplaceKernel
              (η + 2 * (k : ℝ) / ℓ) T a := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro a ha
      exact upperGammaCenteredTruncatedKernel_eq_sum
        ℓ η T n a
    _ = ∑ k ∈ Finset.range (n + 1),
        (∫ a : ℝ in Ioi 0,
          upperCenteredLaplaceKernel
            (η + 2 * (k : ℝ) / ℓ) T a) := by
      apply integral_finsetSum
      intro k hk
      exact upperCenteredLaplaceKernel_integrable
        (upperGammaLaplaceRate_pos hℓ hη k) T
end CohnElkies
