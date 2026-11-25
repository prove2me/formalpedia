-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.cc_toAllS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:20:05.511832+00:00
-- url     : https://prove2.me/submissions/a354190a-2fda-4ea6-b191-b8f2da9334d4

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqSelfOfUnitGerm
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValL
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_cc_subst_eq


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
variable {C : Type} [Field C] [CharZero C] {V : VF C} {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type}
  [∀ o g, Fintype (I o g)]
namespace Formalism.L2.FormalSeriesBounds.VP
theorem _root_.solution (o : Orb) (F : MvPowerSeries (WV (I o)) C) :
    MvPowerSeries.constantCoeff (toAllS o F) = MvPowerSeries.constantCoeff F := by
  unfold toAllS
  exact VP.cc_subst_eq (fun _ => MvPowerSeries.constantCoeff_X _) F
end Formalism.L2.FormalSeriesBounds.VP
