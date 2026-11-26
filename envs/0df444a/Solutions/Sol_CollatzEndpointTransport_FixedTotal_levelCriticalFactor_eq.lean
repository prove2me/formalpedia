-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.levelCriticalFactor_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:35:22.678133+00:00
-- url     : https://prove2.me/submissions/d1f5bb66-ca67-469a-935b-65de562eeafd

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalLevelBadMass
import Definitions.Def_CollatzEndpointTransport_Linear_OptimizedLinearPullbackConstants
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_sourceOddLevel


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (M s : ℕ) (hs : s ≤ M) :
    Real.sqrt
          ((3 : ℝ) ^ (s + 1) /
            (sourceOddLevel M s).card) *
        (∑ y ∈ actualLevelEndpointSet M s,
          (actualLevelFiberCard M s y : ℝ) *
            Real.sqrt (actualLevelFiberCard M s y)) =
      Real.sqrt 3 * actualLevelCriticalContribution M s := by
  have hNnat : 0 < (sourceOddLevel M s).card := by
    rw [card_sourceOddLevel]
    exact Nat.choose_pos hs
  have hN :
      0 < ((sourceOddLevel M s).card : ℝ) := by
    exact_mod_cast hNnat
  have h3s : 0 ≤ (3 : ℝ) ^ s := by positivity
  unfold actualLevelCriticalContribution
  rw [Real.sqrt_div (by positivity)]
  rw [pow_succ]
  rw [Real.sqrt_mul h3s]
  field_simp [ne_of_gt (Real.sqrt_pos.2 hN)]
end CollatzEndpointTransport.FixedTotal
