-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.ev_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:26:47.932431+00:00
-- url     : https://prove2.me/submissions/d014cd2f-04e7-4004-b3db-60f1a514a5da

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_PullbackLogCoordsEvalZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfUnitGerm
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X


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
theorem _root_.solution (f : PS C 2 dd) : ev (n := 2) ![pt C dd 0, pt C dd 1] f = f := by
  have h : (fun q : Fin 2 × Fin dd => (![pt C dd 0, pt C dd 1] : Fin 2 → Pt C 2 dd) q.1 q.2) =
      MvPowerSeries.X := by
    funext ⟨i, k⟩; fin_cases i <;> rfl
  unfold ev
  rw [h, MvPowerSeries.subst_self]
  rfl
end Formalism.L2.FormalSeriesBounds.VP
