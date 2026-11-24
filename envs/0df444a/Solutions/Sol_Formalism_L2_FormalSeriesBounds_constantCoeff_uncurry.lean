-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.constantCoeff_uncurry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:08:09.957624+00:00
-- url     : https://prove2.me/submissions/d4cc00bc-6f43-420f-8ea5-c5f5b14773ac

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes

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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries
variable {C : Type} [Field C]
variable {dd : ℕ}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (f : PS C 1 dd) : constantCoeff (un1 f) = constantCoeff f := by
  rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply]
  show coeff ((0 : Fin dd →₀ ℕ).mapDomain fun x : Fin dd => ((0 : Fin 1), x)) f = coeff 0 f
  rw [Finsupp.mapDomain_zero]
end Formalism.L2.FormalSeriesBounds
