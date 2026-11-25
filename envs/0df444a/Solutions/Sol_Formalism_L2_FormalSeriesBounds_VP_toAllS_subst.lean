-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.toAllS_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:50:01.893947+00:00
-- url     : https://prove2.me/submissions/bd511a0c-5704-4eca-b342-6524d9c3712c

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqSelfOfUnitGerm
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValL
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_subst_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst


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
theorem _root_.solution {κ : Type} [Finite κ] (o : Orb) {E : κ → MvPowerSeries (WV (I o)) C}
    (hE : ∀ x, MvPowerSeries.constantCoeff (E x) = 0) (T : MvPowerSeries κ C) :
    toAllS o (MvPowerSeries.subst E T) = MvPowerSeries.subst (fun x => toAllS o (E x)) T := by
  unfold toAllS
  exact VP.subst_subst hE (fun _ => MvPowerSeries.constantCoeff_X _) T
end Formalism.L2.FormalSeriesBounds.VP
