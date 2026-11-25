-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.inv_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:39:01.117818+00:00
-- url     : https://prove2.me/submissions/6b023239-1558-443e-882e-56a717b165dc

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstantCoeffSinglePointZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IntSProd

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
variable {C : Type} [Field C] {V : VF C} {σ : Type}
namespace Formalism.L2.FormalSeriesBounds.VP
theorem _root_.solution {c : C} (hc : V.v c = 0) : V.Ge 0 c⁻¹ := by
  simp [VF.Ge, AddValuation.map_inv, hc]
end Formalism.L2.FormalSeriesBounds.VP
