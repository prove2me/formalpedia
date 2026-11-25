-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.actK_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:03:11.162844+00:00
-- url     : https://prove2.me/submissions/ed12bead-7ff1-47f9-bb18-36d14f858dca

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValU
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstantCoeffTripleSubstitution
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_toK_eq

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
theorem _root_.solution (x : O) (i : Fin dd) : Y.B.actK C x i = Y.B.A.act x i := by
  unfold FB.actK
  exact toK_eq _
end Formalism.L2.FormalSeriesBounds.VP
