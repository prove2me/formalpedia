-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.elementary_pair_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:16:25.747654+00:00
-- url     : https://prove2.me/submissions/487bbd50-0ecb-48b0-9667-c5efd096dbda

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStab
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_exchangeTwo_self_eq_one
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_elementary_pair_apply_second
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_elementary_pair_support

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
variable {τ κ : Type} [Fintype κ]
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {i i' j j' : κ} (h : E2 ((0 : Fin 2), i) ((1 : Fin 2), j) = E2 ((0 : Fin 2), i') ((1 : Fin 2), j')) :
    i = i' ∧ j = j' := by
  have hne : ∀ x y : κ, ((0 : Fin 2), x) ≠ ((1 : Fin 2), y) := fun x y e => by
    have h01 : (0 : Fin 2) = 1 := congrArg Prod.fst e
    exact absurd h01 (by decide)
  constructor
  · have h1 : E2 ((0 : Fin 2), i') ((1 : Fin 2), j') ((0 : Fin 2), i) ≠ 0 := by
      rw [← h, exchangeTwo_self_eq_one (hne i j)]; exact one_ne_zero
    rcases elementary_pair_support h1 with e | e
    · exact (Prod.mk.inj e).2
    · exact absurd e (hne i j')
  · have h1 : E2 ((0 : Fin 2), i') ((1 : Fin 2), j') ((1 : Fin 2), j) ≠ 0 := by
      rw [← h, elementary_pair_apply_second (hne i j)]; exact one_ne_zero
    rcases elementary_pair_support h1 with e | e
    · exact absurd e.symm (hne i' j)
    · exact (Prod.mk.inj e).2
end Formalism.L2.FormalSeriesBounds
