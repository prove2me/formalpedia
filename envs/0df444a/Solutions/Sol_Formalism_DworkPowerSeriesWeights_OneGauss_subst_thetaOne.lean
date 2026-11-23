-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.OneGauss.subst_thetaOne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:56:51.95531+00:00
-- url     : https://prove2.me/submissions/6fc74137-7814-45af-86cf-43d6a56a0538

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
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_OneGauss_subst_expo
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_OneGauss_thetaOne_eq
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_subst_mvExp
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs


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
theorem _root_.solution {ι : Type} {a : Fin N0 × Fin N1 → MvPowerSeries ι K}
    (hs : MvPowerSeries.HasSubst a)
    (g : Fin N0 × Fin N1 → MvPowerSeries (Fin N0 × Fin N1) K)
    (U : MvPowerSeries (Fin N0 × Fin N1) K) (sgn ep : K) (be : MvPowerSeries (ZMod 2) K)
    (hbe : MvPowerSeries.constantCoeff be = 0) :
    MvPowerSeries.subst a (thetaOne g U sgn ep be) =
      MvPowerSeries.subst a (MvPowerSeries.subst g U) * _root_.Formalism.DworkPowerSeriesWeights.mvExp (expo a sgn ep be) := by
  rw [thetaOne_eq, MvPowerSeries.subst_mul hs,
    subst_mvExp hs _ (cc_expo _ (fun x => MvPowerSeries.constantCoeff_X x) _ _ _ hbe),
    subst_expo hs _ (fun x => MvPowerSeries.constantCoeff_X x)]
  simp only [MvPowerSeries.subst_X hs]
end Formalism.DworkPowerSeriesWeights.OneGauss
