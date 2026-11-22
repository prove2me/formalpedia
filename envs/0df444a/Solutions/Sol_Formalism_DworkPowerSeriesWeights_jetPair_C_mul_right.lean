-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.jetPair_C_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:12:41.2688+00:00
-- url     : https://prove2.me/submissions/ed94e9a7-186e-47d0-96e3-5c6119a7c9ea

import Definitions.Def_Formalism_GaussJetBounds_StatementJ
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP

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
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
variable {K : Type u} [Field K] {ι : Type}
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (c : K) (P : MvPolynomial ι K) (F : MvPowerSeries ι K) :
    jetPair P (MvPowerSeries.C c * F) = c * jetPair P F := by
  simp only [jetPair, MvPowerSeries.coeff_C_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun κ _ => ?_)
  ring
end Formalism.DworkPowerSeriesWeights
