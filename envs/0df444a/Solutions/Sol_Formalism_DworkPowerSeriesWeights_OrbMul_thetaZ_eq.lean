-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.OrbMul.thetaZ_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:56:53.095619+00:00
-- url     : https://prove2.me/submissions/250730e8-b0c7-4991-b34c-bbd1939848d0

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementW
import Definitions.Def_Formalism_GaussJetBounds_ThmAGauss
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneGauss
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OrbMul
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_OrbMul_linSub_idM

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
open Formalism.DworkPowerSeriesWeights.OrbMul
namespace Formalism.DworkPowerSeriesWeights.OrbMul
theorem _root_.solution {K : Type} [NormedField K] [CharZero K] {d N0 N1 : ℕ} [NeZero d]
    (g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) K) (U : MvPowerSeries (ZV d N0 N1) K) (ε : K)
    (be : MvPowerSeries (ZMod d) K) :
    thetaZ g U ε be = MvPowerSeries.subst g U *
      mvExp (ε • bSum (idM : ZV d N0 N1 → ZV d N0 N1 → K) be) := by
  unfold thetaZ
  rw [show (linSub (idM : ZV d N0 N1 → ZV d N0 N1 → K) : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) K) =
      MvPowerSeries.X from funext linSub_idM, MvPowerSeries.subst_self]
  rfl
end Formalism.DworkPowerSeriesWeights.OrbMul
