-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.compose_one_action_eq_actAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:15:47.097312+00:00
-- url     : https://prove2.me/submissions/e0a757ce-a023-4d22-be84-4f2b11e86722

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValU
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstantCoeffTripleSubstitution
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_actK_eq

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
theorem _root_.solution {n : ℕ} (x : O) (a : Pt C n dd) : comp1 (Y.B.actK C x) a = actAt Y x a := by
  funext i
  simp only [comp1, ev, actAt, actK_eq, Matrix.cons_val_fin_one]
end Formalism.L2.FormalSeriesBounds.VP
