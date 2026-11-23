-- Prove2me | solution 1 for CompanionTheory.D.LK.sup_bd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:05:59.675081+00:00
-- url     : https://prove2.me/submissions/03d58a71-897c-44eb-ba36-e13f58ade1ec

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_CreApply
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialBoundedSupport
import Theorems.Thm_CompanionTheory_D_LK_ann_ne
import Theorems.Thm_CompanionTheory_D_LK_tri_ne
import Theorems.Thm_CompanionTheory_D_LK_Tri_cptk
import Theorems.Thm_CompanionTheory_D_LK_bd_ne
import Theorems.Thm_CompanionTheory_D_LK_filter_erase_of_not

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.LK
open Car Formalism.REAL
variable {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace CompanionTheory.D.LK
theorem _root_.solution {ε : Fin n → Bool} (E : Fin n → Fin n → Module.End ℂ V) {B : Finset (Pos n)} {j : ℕ} {x : Cn n V}
    (hx : Sup ε B j x) {A : Finset (Pos n)} (h : bd ε E x A ≠ 0) :
    (A.filter fun i => ¬cpt ε i) = B ∧ (A.filter (cpt ε)).card + 1 = j := by
  rcases bd_ne ε E x A h with ⟨i, hi, h1⟩ | ⟨i, j', k, ht, h1⟩
  · obtain ⟨h2, h3⟩ := ann_ne h1
    obtain ⟨e1, e2⟩ := hx _ h3
    rw [filter_insert, if_neg (not_not.2 hi)] at e1
    rw [filter_insert, if_pos hi, card_insert_of_notMem (fun h => h2 (mem_filter.1 h).1)] at e2
    exact ⟨e1, e2⟩
  · obtain ⟨h2, h3, h4, h5⟩ := tri_ne h1
    obtain ⟨e1, e2⟩ := hx _ h5
    rw [filter_insert, if_neg (not_not.2 ht.1), filter_insert, if_neg (not_not.2 ht.2.1),
      filter_erase_of_not (not_not.2 ht.cptk)] at e1
    rw [filter_insert, if_pos ht.1, card_insert_of_notMem (fun h => h4 (mem_filter.1 h).1), filter_insert,
      if_pos ht.2.1, card_insert_of_notMem (fun h => h3 (mem_filter.1 h).1), filter_erase] at e2
    have := card_erase_add_one (mem_filter.2 ⟨h2, ht.cptk⟩ : k ∈ A.filter (cpt ε))
    exact ⟨e1, by omega⟩
end CompanionTheory.D.LK
