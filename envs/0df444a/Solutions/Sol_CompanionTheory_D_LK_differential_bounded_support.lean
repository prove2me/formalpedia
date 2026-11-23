-- Prove2me | solution 1 for CompanionTheory.D.LK.differential_bounded_support
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:26.770952+00:00
-- url     : https://prove2.me/submissions/82d25d88-fb53-409c-b45f-2cfd1c862d91

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_CreApply
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialBoundedSupport
import Theorems.Thm_CompanionTheory_D_LK_ann_ne
import Theorems.Thm_CompanionTheory_D_LK_tri_ne
import Theorems.Thm_CompanionTheory_D_LK_Tri_cptk
import Theorems.Thm_CompanionTheory_D_LK_bd_sub_ne
import Theorems.Thm_CompanionTheory_D_LK_bd_ne
import Theorems.Thm_CompanionTheory_D_LK_sup_bd
import Theorems.Thm_CompanionTheory_D_LK_pot_insert
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
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
theorem _root_.solution : BdSup := by
  intro n ε V _ _ E
  refine ⟨fun B j x hx A hA => ?_, fun B x hx => ?_, fun ε₀ x h0 hr => ⟨?_, fun A hA i hi hc => ?_⟩,
    fun B j x hx A hA => ?_⟩
  · have := sup_bd E hx hA
    exact ⟨this.1, by omega⟩
  · funext A
    by_contra h
    have := (sup_bd E hx h).2
    omega
  · funext A
    by_contra h
    rcases bd_sub_ne h0 E x A h with ⟨i, h1, h2, h3⟩ | ⟨i, j, k, ht, h2, h3⟩
    · exact h2 (hr _ (ann_ne h3).2 i (mem_insert_self _ _) h1)
    · have h5 := (tri_ne h3).2.2.2
      exact h2 ⟨hr _ h5 i (mem_insert_self _ _) ht.1, hr _ h5 j (mem_insert_of_mem (mem_insert_self _ _)) ht.2.1⟩
  · rcases bd_ne ε E x A hA with ⟨i', _, h1⟩ | ⟨i', j, k, ht, h1⟩
    · exact hr _ (ann_ne h1).2 i (mem_insert_of_mem hi) hc
    · by_cases hk : i = k
      · exact hk ▸ ht.cptk
      · exact hr _ (tri_ne h1).2.2.2 i (mem_insert_of_mem (mem_insert_of_mem (mem_erase.2 ⟨hk, hi⟩))) hc
  · have hne : bd (allT n) E x A ≠ bd ε E x A := fun h => hA (by rw [Pi.sub_apply, h, sub_self])
    have hcard : ∀ S, x S ≠ 0 → S.card = B.card + j := fun S hS => by
      obtain ⟨e1, e2⟩ := hx S hS
      rw [← e1, ← e2, add_comm, card_filter_add_card_filter_not]
    have hpos : ∀ i : Pos n, (i.1.1 : ℕ) < i.1.2 ∧ (i.1.2 : ℕ) < n := fun i => ⟨i.2, i.1.2.2⟩
    rcases bd_sub_ne (ε₀ := allT n) (fun _ _ _ => rfl) E x A hne with ⟨i, -, h2, h3⟩ | ⟨i, j', k, ht, h2, h3⟩
    · obtain ⟨h4, h5⟩ := ann_ne h3
      have e1 := (hx _ h5).1
      have e2 := hcard _ h5
      rw [card_insert_of_notMem h4] at e2
      rw [filter_insert, if_pos h2] at e1
      rw [← e1, pot_insert (fun h => h4 (mem_filter.1 h).1)]
      have := hpos i
      exact ⟨by omega, by rw [e1]; exact e2⟩
    · obtain ⟨h4, h5, h6, h7⟩ := tri_ne h3
      have e1 := (hx _ h7).1
      have e2 := hcard _ h7
      rw [card_insert_of_notMem h6, card_insert_of_notMem h5] at e2
      have e3 := card_erase_add_one h4
      refine ⟨?_, by omega⟩
      obtain ⟨-, -, t1, t2, t3⟩ := ht
      have pi := hpos i
      have pj := hpos j'
      have pk := hpos k
      have v1 : (i.1.2 : ℕ) = j'.1.1 := congrArg Fin.val t1
      have v2 : (k.1.1 : ℕ) = i.1.1 := congrArg Fin.val t2
      have v3 : (k.1.2 : ℕ) = j'.1.2 := congrArg Fin.val t3
      set R := (A.erase k).filter fun i => ¬cpt ε i with hR
      have hjR : j' ∉ R := fun h => h5 (mem_filter.1 h).1
      have hiR : i ∉ R := fun h => h6 (mem_insert_of_mem (mem_filter.1 h).1)
      have hij : i ∉ insert j' R := fun h => h6 (by
        rcases mem_insert.1 h with h | h
        · exact h ▸ mem_insert_self _ _
        · exact absurd h hiR)
      have hA' : (A.filter fun i => ¬cpt ε i) = if ¬cpt ε k then insert k R else R := by
        conv_lhs => rw [← insert_erase h4, filter_insert]
      have hkR : k ∉ R := fun h => notMem_erase k A (mem_filter.1 h).1
      have hk : cpt ε k ↔ (cpt ε i ↔ cpt ε j') := by
        simp only [cpt, t2, t3, ← t1]
        cases ε i.1.1 <;> cases ε i.1.2 <;> cases ε j'.1.2 <;> simp
      rw [hA', ← e1, filter_insert, filter_insert, ← hR]
      by_cases ci : cpt ε i <;> by_cases cj : cpt ε j'
      · exact absurd ⟨ci, cj⟩ h2
      · have ck : ¬cpt ε k := by rw [hk]; tauto
        rw [if_pos ck, if_neg (not_not.2 ci), if_pos cj, pot_insert hkR, pot_insert hjR]; omega
      · have ck : ¬cpt ε k := by rw [hk]; tauto
        rw [if_pos ck, if_pos ci, if_neg (not_not.2 cj), pot_insert hkR, pot_insert hiR]; omega
      · have ck : cpt ε k := by rw [hk]; tauto
        rw [if_neg (not_not.2 ck), if_pos ci, if_pos cj, pot_insert hij, pot_insert hjR]; omega
end CompanionTheory.D.LK
