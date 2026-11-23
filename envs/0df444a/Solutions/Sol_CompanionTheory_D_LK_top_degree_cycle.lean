-- Prove2me | solution 1 for CompanionTheory.D.LK.top_degree_cycle
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:25.517596+00:00
-- url     : https://prove2.me/submissions/de3fef3b-ec1b-4cba-a545-d7fa0dda8a34

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_CreApply
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialBoundedSupport
import Theorems.Thm_CompanionTheory_D_LK_bd_apply
import Theorems.Thm_CompanionTheory_D_LK_tri_ne
import Theorems.Thm_CompanionTheory_D_LK_Tri_cptk
import Theorems.Thm_CompanionTheory_D_LK_wt_om
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
import Theorems.Thm_CompanionTheory_D_LK_Car_ann_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Finset
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.LK
open Car Formalism.REAL
variable {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace CompanionTheory.D.LK
theorem _root_.solution : TopCycle := by
  intro n ε V _ _ E μ v
  refine ⟨wt_om ε, fun hv => ⟨?_, fun c => ?_⟩⟩
  · funext A
    rw [bd_apply, Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero, Pi.zero_apply]
    · refine fun i _ => Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
      split_ifs with ht
      · by_contra h
        obtain ⟨h1, -, -, h4⟩ := tri_ne h
        have e : insert i (insert j (A.erase k)) = om ε := by
          by_contra h'; exact h4 (Pi.single_eq_of_ne h' _)
        have ci : cpt ε i := (mem_filter.1 (e ▸ mem_insert_self _ _ : i ∈ om ε)).2
        have cj : cpt ε j := (mem_filter.1 (e ▸ mem_insert_of_mem (mem_insert_self _ _) : j ∈ om ε)).2
        have ck : k ∈ om ε := mem_filter.2 ⟨mem_univ _, Tri.cptk ⟨ci, cj, ht.2.2⟩⟩
        rw [← e] at ck
        obtain ⟨-, -, t1, t2, t3⟩ := ht
        have pi := i.2
        have pj := j.2
        rcases mem_insert.1 ck with h | h
        · subst h; rw [← t1, t3] at pj; exact lt_irrefl _ pj
        · rcases mem_insert.1 h with h | h
          · subst h; rw [← t2, t1] at pi; exact lt_irrefl _ pi
          · exact notMem_erase _ _ h
      · rfl
    · intro i _
      rw [if_pos rfl, ann_apply]
      split_ifs with hi
      · exact map_zero _
      · by_cases e : insert i A = om ε
        · rw [e, Pi.single_eq_same, map_smul,
            hv.2 _ _ i.2 (mem_filter.1 (e ▸ mem_insert_self _ _ : i ∈ om ε)).2, smul_zero]
        · rw [Pi.single_eq_of_ne e, smul_zero, map_zero]
  · funext A
    show E c c ((Pi.single (om ε) v : Cn n V) A) + (_ : ℂ) • (Pi.single (om ε) v : Cn n V) A =
      (_ : ℂ) • (Pi.single (om ε) v : Cn n V) A
    by_cases e : A = om ε
    · subst e
      rw [Pi.single_eq_same, hv.1, filter_true_of_mem (fun _ _ => rfl), wt_om, ← add_smul]
      simp
    · simp [Pi.single_eq_of_ne e]
end CompanionTheory.D.LK
