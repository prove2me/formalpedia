-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.map_mvExp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:02:46.543966+00:00
-- url     : https://prove2.me/submissions/958cc12c-5009-4bc6-bc51-1e4da328dbe8

import Definitions.Def_Formalism_GaussJetBounds_FrameJetEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FJEval

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
variable {F K : Type} [NormedField F] [CharZero F] [NormedField K] [CharZero K] (φ : F →+* K)
  {d N0 N1 : ℕ} [NeZero d] {ι : Type} [Fintype ι]
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (f : MvPowerSeries ι F) (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.map φ (mvExp f) = mvExp (MvPowerSeries.map φ f) := by
  unfold mvExp
  rw [PowerSeries.subst_def, PowerSeries.subst_def,
    MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => hf)]
  congr 1
  exact PowerSeries.map_exp φ
end Formalism.DworkPowerSeriesWeights
