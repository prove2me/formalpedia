-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.OneGauss.map_thetaOne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:04:26.15705+00:00
-- url     : https://prove2.me/submissions/4cf7df03-73f9-4395-96c8-30585ba97bff

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
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_OneGauss_cc_expo
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_OneGauss_map_expo
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_OneGauss_thetaOne_eq
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_map_mvExp
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_map_mvExp


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
variable {K : Type} [NormedField K] [CharZero K] {N0 N1 : ℕ}
namespace Formalism.DworkPowerSeriesWeights.OneGauss
theorem _root_.solution {F : Type} [NormedField F] [CharZero F] (φ : F →+* K)
    (g : Fin N0 × Fin N1 → MvPowerSeries (Fin N0 × Fin N1) F)
    (hg : ∀ y, MvPowerSeries.constantCoeff (g y) = 0)
    (U : MvPowerSeries (Fin N0 × Fin N1) F) (sgn ep : F) (be : MvPowerSeries (ZMod 2) F)
    (hbe : MvPowerSeries.constantCoeff be = 0) :
    MvPowerSeries.map φ (thetaOne g U sgn ep be) =
      thetaOne (fun y => MvPowerSeries.map φ (g y)) (MvPowerSeries.map φ U) (φ sgn) (φ ep)
        (MvPowerSeries.map φ be) := by
  rw [thetaOne_eq, thetaOne_eq, map_mul,
    MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero hg),
    Transfer.map_mvExp φ (cc_expo _ (fun x => MvPowerSeries.constantCoeff_X x) _ _ _ hbe),
    map_expo φ _ (fun x => MvPowerSeries.constantCoeff_X x)]
  simp only [MvPowerSeries.map_X]
end Formalism.DworkPowerSeriesWeights.OneGauss
