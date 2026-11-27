-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.eval_points_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:08:19.639008+00:00
-- url     : https://prove2.me/submissions/8708f3fd-5184-486c-8ba6-294345a7e2c5

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RankMaximalOfNondegenerate
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {dd : ℕ} (f : PS C 2 dd) : ev (n := 2) ![pt C dd 0, pt C dd 1] f = f := by
  unfold ev
  have e : (fun q : Fin 2 × Fin dd => (![pt C dd 0, pt C dd 1] : Fin 2 → Pt C 2 dd) q.1 q.2) =
      fun q => (MvPowerSeries.X q : PS C 2 dd) := by
    funext ⟨k, j⟩
    fin_cases k <;> rfl
  rw [e, MvPowerSeries.subst_self]
  rfl
end Formalism.L2.FormalSeriesBounds
