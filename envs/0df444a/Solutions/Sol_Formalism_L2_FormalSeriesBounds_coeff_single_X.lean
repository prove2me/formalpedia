-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.coeff_single_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:57:13.381531+00:00
-- url     : https://prove2.me/submissions/58a09804-6760-4299-93fc-ca6f02869bc5

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStab
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries
variable {C : Type} [Field C]
variable {dd : ℕ}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (g : Fin 2) (j k : Fin dd) :
    coeff (Finsupp.single (g, k) 1) (X (g, j) : PS C 2 dd) = if j = k then 1 else 0 := by
  rw [coeff_X]
  by_cases h : j = k
  · subst h; simp
  · rw [if_neg h, if_neg]
    intro e
    exact h (Prod.mk.inj ((Finsupp.single_left_inj one_ne_zero).1 e)).2.symm
end Formalism.L2.FormalSeriesBounds
