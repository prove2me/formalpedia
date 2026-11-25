-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.actAt_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:36:16.863769+00:00
-- url     : https://prove2.me/submissions/fde5c197-6ee2-47c2-a41a-0f302c1f7549

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FirstPartialLawAtPoints
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoordinateChangeComp1IntertwinesAction
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_subst_zeroPt
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_const


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
theorem _root_.solution (x : O) : actAt Y x (fun _ : Fin dd => (0 : MvPowerSeries τ C)) = fun _ => 0 := by
  funext i
  unfold actAt
  rw [subst_zeroPt, Y.B.A.const, map_zero]
end Formalism.L2.FormalSeriesBounds.VP
