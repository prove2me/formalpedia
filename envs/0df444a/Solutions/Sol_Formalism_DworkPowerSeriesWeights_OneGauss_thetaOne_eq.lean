-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.OneGauss.thetaOne_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:02:20.385812+00:00
-- url     : https://prove2.me/submissions/026c54b5-5598-4cc8-950c-3250558c0f68

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
theorem _root_.solution (g : Fin N0 × Fin N1 → MvPowerSeries (Fin N0 × Fin N1) K)
    (U : MvPowerSeries (Fin N0 × Fin N1) K) (sgn ep : K) (be : MvPowerSeries (ZMod 2) K) :
    thetaOne g U sgn ep be = MvPowerSeries.subst g U *
      _root_.Formalism.DworkPowerSeriesWeights.mvExp (expo (fun x => (MvPowerSeries.X x : MvPowerSeries (Fin N0 × Fin N1) K)) sgn ep be) :=
  rfl
end Formalism.DworkPowerSeriesWeights.OneGauss
