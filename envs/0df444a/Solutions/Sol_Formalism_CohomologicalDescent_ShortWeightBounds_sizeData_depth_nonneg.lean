-- Prove2me | solution 1 for Formalism.CohomologicalDescent.ShortWeightBounds.sizeData_depth_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:39:47.531029+00:00
-- url     : https://prove2.me/submissions/8c26fd20-472c-4962-b698-963378a2fe54

import Definitions.Def_Formalism_PieriBlockIdeals_LatticeInclusionRealSettingAlt
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightBounds
import Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_one_le_h

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
theorem _root_.solution {ι : Type} (W : Wts ι) (P : Par) (hH : P.Hyp) (J : ℕ → ℕ) (τ : ι) (l : ℕ) :
    0 ≤ (W.sizeData₂ P J).depth P τ l := by
  have hh := one_le_h P hH
  unfold SizeData₂.depth
  have h1 : 0 ≤ ((W.sizeData₂ P J).q τ : ℝ) * P.h := mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have h2 : 0 ≤ ((l : ℝ) * ((W.sizeData₂ P J).mwF τ l : ℝ) + ((W.sizeData₂ P J).mw τ l : ℝ)) *
      ((P.t : ℝ) + 2 * (P.kap l : ℝ)) := by positivity
  linarith
end Formalism.CohomologicalDescent.ShortWeightBounds
