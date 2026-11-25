-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.toK_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:37:15.544691+00:00
-- url     : https://prove2.me/submissions/cfe193be-c6bc-44d0-b468-1d9d9c97f346

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValU
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstantCoeffTripleSubstitution

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
namespace Formalism.L2.FormalSeriesBounds.VP
theorem _root_.solution {n : ℕ} (f : PS C n dd) : FB.toK C f = f := by
  unfold FB.toK
  simp
end Formalism.L2.FormalSeriesBounds.VP
