-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.SelfConjugateGermZero.uncurry_log_constantCoeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:22:36.362779+00:00
-- url     : https://prove2.me/submissions/dfa9f1bd-1f3c-4f3f-811e-4918b6202401

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeneralGermZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_UncurryLogConstantCoeff

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
open Formalism.L2.FormalSeriesBounds.SelfConjugateGermZero
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ FormalGermZero GeneralGermZero
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
namespace Formalism.L2.FormalSeriesBounds.SelfConjugateGermZero
theorem _root_.solution (Y : FBChart C V O dd) (j : Fin dd) : MvPowerSeries.constantCoeff (un1 (Y.lg j)) = 0 := by
  show MvPowerSeries.coeff (Finsupp.mapDomain (fun x : Fin dd => ((0 : Fin 1), x)) 0) (Y.lg j) = 0
  rw [Finsupp.mapDomain_zero, Y.lg_lin j 0 (by simp)]
  simp
end Formalism.L2.FormalSeriesBounds.SelfConjugateGermZero
