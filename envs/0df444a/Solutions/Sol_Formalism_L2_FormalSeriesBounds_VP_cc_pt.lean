-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.cc_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:38:44.666798+00:00
-- url     : https://prove2.me/submissions/4119c6ce-e816-4848-9889-da8ae5e32fa6

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
theorem _root_.solution {n : ℕ} (g : Fin n) (i : Fin dd) : MvPowerSeries.constantCoeff (pt C dd g i) = 0 := MvPowerSeries.constantCoeff_X _
end Formalism.L2.FormalSeriesBounds.VP
