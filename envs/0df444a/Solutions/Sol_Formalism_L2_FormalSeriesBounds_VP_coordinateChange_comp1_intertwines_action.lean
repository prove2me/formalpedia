-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.coordinateChange_comp1_intertwines_action
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:18:26.744487+00:00
-- url     : https://prove2.me/submissions/4a83058f-bacd-4f26-92d8-80157c1d97e1

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FirstPartialLawAtPoints
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoordinateChangeComp1IntertwinesAction
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_GoodPt_act


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
theorem _root_.solution {n : ℕ} (x : O) (a : Pt C n dd) : comp1 (Y.B.A.act x) a = actAt Y x a := by
  unfold actAt
  unfold comp1
  funext i
  unfold ev
  first
  | rfl
  | (congr 1; funext q; simp)
  | (congr 1; funext q; skip)
end Formalism.L2.FormalSeriesBounds.VP
