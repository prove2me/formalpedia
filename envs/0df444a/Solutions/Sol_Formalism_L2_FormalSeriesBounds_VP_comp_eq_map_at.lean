-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.comp_eq_map_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:52:01.39937+00:00
-- url     : https://prove2.me/submissions/5f3c1c6e-a019-4d0e-a4cc-013e5b92e2e5

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValBr
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValCr

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
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ τ' : Type}
namespace Formalism.L2.FormalSeriesBounds.VP
theorem _root_.solution {n : ℕ} (ε : Pt C 1 dd) (a : Pt C n dd) : comp1 ε a = mapAt ε a := by
  unfold comp1 mapAt ev
  funext i
  congr 1
  funext p
  first
    | (rw [Fin.fin_one_eq_zero p.1]; rfl)
    | (simp [Fin.fin_one_eq_zero p.1])
end Formalism.L2.FormalSeriesBounds.VP
