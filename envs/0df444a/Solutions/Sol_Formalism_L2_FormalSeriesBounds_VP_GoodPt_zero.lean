-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.GoodPt.zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:08:42.53137+00:00
-- url     : https://prove2.me/submissions/ad3fa836-b308-445e-850a-dfb7c442cb02

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfBiadditiveCross
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FirstPartialLawAtPoints

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
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open Formalism.L2.FormalSeriesBounds.VP
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ : Type}
variable (Y : FBChart C V O dd)
namespace Formalism.L2.FormalSeriesBounds.VP
namespace GoodPt
theorem _root_.solution : GoodPt V (fun _ : Fin dd => (0 : MvPowerSeries τ C)) := by
  refine ⟨fun _ => map_zero _, fun _ => ?_⟩
  unfold IntS
  intro μ
  rw [map_zero]
  unfold VF.Ge
  first
    | simp
    | exact le_top
    | (simp [VF.v]; done)
end GoodPt
end Formalism.L2.FormalSeriesBounds.VP
