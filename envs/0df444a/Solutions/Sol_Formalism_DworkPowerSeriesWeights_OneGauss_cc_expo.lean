-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.OneGauss.cc_expo
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:15:37.606617+00:00
-- url     : https://prove2.me/submissions/f70dbfc8-c7d5-425b-97d3-323dc746a5e4

import Definitions.Def_Formalism_GaussJetBounds_StatementU
import Definitions.Def_Formalism_GaussJetBounds_OneLetterRadius
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GField
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Transfer
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FJEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Labels
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneGauss
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_OneGauss_cc_smul

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
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
open Formalism.DworkPowerSeriesWeights.OneGauss
variable {K : Type} [Field K] {τ ι : Type} [Fintype τ]
namespace Formalism.DworkPowerSeriesWeights.OneGauss
theorem _root_.solution (v : τ → MvPowerSeries ι K) (hv : ∀ x, MvPowerSeries.constantCoeff (v x) = 0)
    (sgn ep : K) (be : MvPowerSeries (ZMod 2) K) (hbe : MvPowerSeries.constantCoeff be = 0) :
    MvPowerSeries.constantCoeff (expo v sgn ep be) = 0 := by
  unfold expo
  refine cc_smul _ ?_
  rw [map_sum]
  refine Finset.sum_eq_zero fun x _ => ?_
  exact MvPowerSeries.constantCoeff_subst_eq_zero
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => cc_smul _ (hv x))
    (fun s => cc_smul _ (hv x)) hbe
end Formalism.DworkPowerSeriesWeights.OneGauss
