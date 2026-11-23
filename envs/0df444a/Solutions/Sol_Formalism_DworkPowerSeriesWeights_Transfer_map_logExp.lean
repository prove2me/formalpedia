-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.Transfer.map_logExp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:00:31.902895+00:00
-- url     : https://prove2.me/submissions/e023113b-7c6f-4ece-aae1-e52b63a7151a

import Definitions.Def_Formalism_GaussJetBounds_FrameJetEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Transfer
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_map_letterLog
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_cc_letterLog
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_map_mvExp

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
open Formalism.IncomingBounds MvPowerSeries
open Formalism.DworkPowerSeriesWeights.Transfer
variable {F K : Type} [NormedField F] [CharZero F] [NormedField K] [CharZero K] (φ : F →+* K)
namespace Formalism.DworkPowerSeriesWeights.Transfer
theorem _root_.solution {d : ℕ} [NeZero d] (l : ℕ) {f : MvPowerSeries (V2 d) F}
    (h : constantCoeff f = 0) :
    map φ (subst (letterLog (K := F) l) (mvExp f)) =
      subst (letterLog (K := K) l) (mvExp (map φ f)) := by
  have hL : ∀ x : V2 d, MvPowerSeries.constantCoeff (letterLog (K := F) l x) = 0 := cc_letterLog l
  rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero hL), map_mvExp φ h]
  congr 1
  funext x
  exact map_letterLog φ l x
end Formalism.DworkPowerSeriesWeights.Transfer
