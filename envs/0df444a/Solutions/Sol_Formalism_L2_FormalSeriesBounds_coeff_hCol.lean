-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.coeff_hCol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:22:33.322835+00:00
-- url     : https://prove2.me/submissions/be8e33aa-bd74-4b21-ac60-b827c7228003

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStab
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePCartSelfSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStabSelf
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_rename_outside
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_subst_rename_inj


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
theorem _root_.solution (h : PS C 2 dd) (col c1 c2 : Fin 2) (i j : Fin dd) :
    coeff (E2 ((0 : Fin 2), (c1, i)) ((1 : Fin 2), (c2, j))) (hCol col h) =
      if c1 = col ∧ c2 = col then coeff (E2 ((0 : Fin 2), i) ((1 : Fin 2), j)) h else 0 := by
  unfold hCol
  split_ifs with hc
  · obtain ⟨h1, h2⟩ := hc
    rw [h1, h2]
    have hφ : Function.Injective (fun p : Fin 2 × Fin dd => (p.1, (col, p.2))) := by
      intro a b hab
      simp only [Prod.mk.injEq] at hab
      exact Prod.ext hab.1 hab.2.2
    have he : E2 ((0 : Fin 2), (col, i)) ((1 : Fin 2), (col, j)) =
        (E2 ((0 : Fin 2), i) ((1 : Fin 2), j)).mapDomain (fun p : Fin 2 × Fin dd => (p.1, (col, p.2))) := by
      simp [E2, Finsupp.mapDomain_add, Finsupp.mapDomain_single]
    rw [he, coeff_subst_rename_inj _ hφ]
  · by_cases h1 : c1 = col
    · have h2 : c2 ≠ col := fun h2 => hc ⟨h1, h2⟩
      refine coeff_rename_outside _ h (E2 _ _) (s := ((1 : Fin 2), (c2, j))) ?_ ?_
      · simp [E2, Finsupp.single_apply]
      · intro x hx
        simp only [Prod.mk.injEq] at hx
        exact h2 hx.2.1.symm
    · refine coeff_rename_outside _ h (E2 _ _) (s := ((0 : Fin 2), (c1, i))) ?_ ?_
      · simp [E2, Finsupp.single_apply]
      · intro x hx
        simp only [Prod.mk.injEq] at hx
        exact h1 hx.2.1.symm
end Formalism.L2.FormalSeriesBounds
