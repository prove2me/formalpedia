-- Prove2me | solution 1 for Formalism.CohomologicalDescent.ShortWeightBounds.depth_nat_le_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:40:29.087515+00:00
-- url     : https://prove2.me/submissions/72b25f5d-bf05-496e-8454-729fc20d224b

import Definitions.Def_Formalism_PieriBlockIdeals_LatticeInclusionRealSettingAlt
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightBounds
import Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_kappa_floor_holds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.ShortWeightBounds
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds
namespace Formalism.CohomologicalDescent.ShortWeightBounds
theorem _root_.solution : DepthNatLe := by
  intro P ι W l τ hh hl
  unfold Wts.iW
  apply Nat.le_floor
  rw [← kappa_floor_holds P l hl]
  have h1 : ((h0 P : ℕ) : ℝ) ≤ P.h := Nat.floor_le hh
  show _ ≤ (W.q τ : ℝ) * P.h
    + ((l : ℝ) * (W.mwF P τ l : ℝ) + (W.mw P τ l : ℝ)) * ((P.t : ℝ) + 2 * (P.kap l : ℝ))
  push_cast
  have h2 : (W.q τ : ℝ) * (h0 P : ℝ) ≤ (W.q τ : ℝ) * P.h :=
    mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
  linarith
end Formalism.CohomologicalDescent.ShortWeightBounds
