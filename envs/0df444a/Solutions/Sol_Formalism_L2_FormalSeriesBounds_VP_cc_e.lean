-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.cc_e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:33:13.885824+00:00
-- url     : https://prove2.me/submissions/176972d2-8af9-47de-9c8c-f2e2d7e0b726

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_PullbackLogCoordsEvalZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfUnitGerm

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
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
variable (Y : FBChart C V O dd)
namespace Formalism.L2.FormalSeriesBounds.VP
theorem _root_.solution (k : Fin dd) : MvPowerSeries.constantCoeff (e Y k) = 0 := by
  have h := Y.ex_const k
  change MvPowerSeries.coeff (Finsupp.mapDomain (fun x : Fin dd => ((0 : Fin 1), x)) 0) (Y.ex k) = 0
  rw [Finsupp.mapDomain_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h]
end Formalism.L2.FormalSeriesBounds.VP
