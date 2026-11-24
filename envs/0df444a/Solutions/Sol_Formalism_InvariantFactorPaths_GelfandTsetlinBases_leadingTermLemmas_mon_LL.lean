-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas.mon_LL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:55:28.821084+00:00
-- url     : https://prove2.me/submissions/ef018fe8-4496-4c54-8b0a-543efc4a9709

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Lemmata_GeneralBFactRightFurther_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_key_lt
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_mon_apply

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
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
variable {n : ℕ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
theorem _root_.solution {m : ℕ} {r c : Fin m → Fin n} (hr : StrictMono r) (hc : StrictMono c)
    (π : Equiv.Perm (Fin m)) (hπ : π ≠ 1) : LL key (mon r c π) (mon r c 1) := by
  classical
  obtain ⟨a, ha, hmin⟩ : ∃ a, π a ≠ a ∧ ∀ i, i < a → π i = i := by
    have hne : (univ.filter fun a => π a ≠ a).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      apply hπ
      ext1 a
      by_contra hc'
      have : a ∈ univ.filter fun a => π a ≠ a := Finset.mem_filter.2 ⟨Finset.mem_univ a, hc'⟩
      rw [h] at this
      exact absurd this (Finset.notMem_empty _)
    obtain ⟨a, haS, hmin⟩ := Finset.exists_min_image _ id hne
    refine ⟨a, (Finset.mem_filter.1 haS).2, fun i hi => ?_⟩
    by_contra hc'
    exact absurd (hmin i (Finset.mem_filter.2 ⟨Finset.mem_univ i, hc'⟩)) (not_le.2 hi)
  have hgt : a < π a := by
    rcases lt_or_gt_of_ne ha with h | h
    · exact absurd (π.injective (hmin _ h)) ha
    · exact h
  refine ⟨(r a, c a), ?_, ?_⟩
  · rw [mon_apply, mon_apply]
    have h0 : (∑ i, if (r i = (r a, c a).1 ∧ c (π i) = (r a, c a).2) then 1 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [if_neg]
      rintro ⟨h1, h2⟩
      have := hr.injective h1
      subst this
      exact ha (hc.injective h2)
    rw [h0]
    have h1 := Finset.single_le_sum
      (f := fun i => if (r i = (r a, c a).1 ∧ c ((1 : Equiv.Perm (Fin m)) i) = (r a, c a).2) then 1 else 0)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
    simp only [Equiv.Perm.coe_one, id_eq, and_self, if_true] at h1
    simp only [Equiv.Perm.coe_one, id_eq]
    omega
  · intro y hy
    rw [key_lt] at hy
    simp only at hy
    rw [mon_apply, mon_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine if_congr ?_ rfl rfl
    rw [Equiv.Perm.one_apply]
    rcases lt_trichotomy i a with h | h | h
    · rw [hmin i h]
    · subst h
      constructor
      · rintro ⟨h1, h2⟩
        exfalso
        rcases hy with hy | ⟨_, hy⟩
        · rw [← h1] at hy; exact lt_irrefl _ hy
        · rw [← h2] at hy; exact absurd (hc hgt) (not_lt.2 hy.le)
      · rintro ⟨h1, h2⟩
        exfalso
        rcases hy with hy | ⟨_, hy⟩
        · rw [← h1] at hy; exact lt_irrefl _ hy
        · rw [← h2] at hy; exact lt_irrefl _ hy
    · have hlt : y.1 < r i := by
        rcases hy with hy | ⟨hy, _⟩
        · exact hy.trans (hr h)
        · rw [hy]; exact hr h
      constructor <;> rintro ⟨h1, _⟩ <;> exact absurd h1 hlt.ne'
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
