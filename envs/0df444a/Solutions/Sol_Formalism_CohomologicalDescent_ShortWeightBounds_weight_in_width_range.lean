-- Prove2me | solution 1 for Formalism.CohomologicalDescent.ShortWeightBounds.weight_in_width_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:23:47.38119+00:00
-- url     : https://prove2.me/submissions/c589827d-f820-499f-b449-47a319937ecc

import Definitions.Def_Formalism_PieriBlockIdeals_LatticeInclusionRealSettingAlt
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightBounds

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
theorem _root_.solution {ι : Type} {W : Wts ι} {P : Par} (hW : W.Ok P) (τ : ι) (a : ℕ) (ha : a < P.Nr) :
    W.U P τ (P.Nr - 1) ≤ UN P.Nr (W.lam τ) a ∧
      UN P.Nr (W.lam τ) a ≤ W.U P τ (P.Nr - 1) + ((W.width P τ).toNat : ℤ) := by
  have h1 := hW.anti τ a (P.Nr - 1) (by omega) (by omega)
  have h2 := hW.anti τ 0 a (by omega) ha
  have h3 := hW.anti τ 0 (P.Nr - 1) (by omega) (by omega)
  unfold Wts.width Wts.U UN
  omega
end Formalism.CohomologicalDescent.ShortWeightBounds
