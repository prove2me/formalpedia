-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.coeff_E2_sum_hCol_eq_ite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:40:13.797285+00:00
-- url     : https://prove2.me/submissions/954ff150-ea28-4f14-ba88-7ac488468d41

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStab
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePCartSelfSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStabSelf
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_hCol
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
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} {I0 : Type} [Fintype I0]
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (h : PS C 2 dd) (c1 c2 : Fin 2) (i j : Fin dd) :
    coeff (E2 ((0 : Fin 2), (c1, i)) ((1 : Fin 2), (c2, j))) (∑ col, hCol col h) =
      if c1 = c2 then coeff (E2 ((0 : Fin 2), i) ((1 : Fin 2), j)) h else 0 := by
  rw [map_sum]
  simp only [coeff_hCol]
  rw [Fin.sum_univ_two]
  by_cases h12 : c1 = c2
  · subst h12
    fin_cases c1 <;> simp
  · fin_cases c1 <;> fin_cases c2 <;> simp_all
end Formalism.L2.FormalSeriesBounds
