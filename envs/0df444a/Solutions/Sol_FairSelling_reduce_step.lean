-- Prove2me | solution 1 for FairSelling.reduce_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:28:45.496383+00:00
-- url     : https://prove2.me/submissions/d413741f-366c-4ba6-9508-175b4d07b669

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Theorems.Thm_FairSelling_vbarSum_union

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (hp : ∀ g, 0 ≤ p g) (r : ℝ)
    (A : Fin 2 → Finset G) (s : Finset G) (q : Fin 2 → ℝ)
    (hcfg : Config w p r A s q) (hcard : 2 ≤ s.card) :
    ∃ (A' : Fin 2 → Finset G) (s' : Finset G) (q' : Fin 2 → ℝ),
      Config w p r A' s' q' ∧ s'.card < s.card := by
  classical
  obtain ⟨hdisjA, hdisjs, hcover, hq0, hsat, hge⟩ := hcfg
  have hne : s.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨g, hgs, hgmin⟩ := s.exists_min_image p hne
  have hpg : 0 ≤ p g := hp g
  have hgA : ∀ k, g ∉ A k := fun k => Finset.disjoint_left.mp (hdisjs k) hgs
  have hsumbound : 2 * p g ≤ ∑ h ∈ s, p h := by
    calc 2 * p g ≤ (s.card : ℝ) * p g := by
          apply mul_le_mul_of_nonneg_right _ hpg; exact_mod_cast hcard
      _ = ∑ _h ∈ s, p g := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ h ∈ s, p h := Finset.sum_le_sum (fun h hh => hgmin h hh)
  have hq01 : q 0 + q 1 = ∑ h ∈ s, p h := by rw [← Fin.sum_univ_two q]; exact hsat
  have key : ∀ i j : Fin 2, i ≠ j → p g ≤ q i →
      ∃ (A' : Fin 2 → Finset G) (s' : Finset G) (q' : Fin 2 → ℝ),
        Config w p r A' s' q' ∧ s'.card < s.card := by
    intro i j hij hqi
    have hk : ∀ k : Fin 2, k = i ∨ k = j := fun k => by omega
    refine ⟨Function.update A i (A i ∪ {g}), s.erase g, Function.update q i (q i - p g),
      ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, Finset.card_erase_lt_of_mem hgs⟩
    · intro a b hab
      rcases hk a with ha | ha <;> rcases hk b with hb | hb
      · exact absurd (ha.trans hb.symm) hab
      · subst a; subst b
        rw [Function.update_self, Function.update_of_ne (Ne.symm hij), Finset.disjoint_union_left]
        exact ⟨hdisjA i j hij, Finset.disjoint_singleton_left.mpr (hgA j)⟩
      · subst a; subst b
        rw [Function.update_self, Function.update_of_ne (Ne.symm hij), Finset.disjoint_union_right]
        exact ⟨hdisjA j i (Ne.symm hij), Finset.disjoint_singleton_right.mpr (hgA j)⟩
      · exact absurd (ha.trans hb.symm) hab
    · intro k
      by_cases hki : k = i
      · subst k; rw [Function.update_self, Finset.disjoint_union_right]
        refine ⟨Finset.disjoint_of_subset_left (Finset.erase_subset _ _) (hdisjs i), ?_⟩
        exact Finset.disjoint_singleton_right.mpr (fun h => (Finset.mem_erase.mp h).1 rfl)
      · rw [Function.update_of_ne hki]
        exact Finset.disjoint_of_subset_left (Finset.erase_subset _ _) (hdisjs k)
    · apply Finset.eq_univ_of_forall
      intro x
      have hx : x ∈ s ∪ Finset.univ.biUnion A := by rw [hcover]; exact Finset.mem_univ x
      simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and] at hx ⊢
      rcases hx with hxs | ⟨k, hxk⟩
      · by_cases hxg : x = g
        · refine Or.inr ⟨i, ?_⟩
          rw [Function.update_self]
          exact Finset.mem_union_right _ (by rw [hxg]; exact Finset.mem_singleton_self g)
        · exact Or.inl (Finset.mem_erase.mpr ⟨hxg, hxs⟩)
      · refine Or.inr ⟨k, ?_⟩
        by_cases hki : k = i
        · subst k; rw [Function.update_self]; exact Finset.mem_union_left _ hxk
        · rw [Function.update_of_ne hki]; exact hxk
    · intro k
      by_cases hki : k = i
      · subst k; rw [Function.update_self]; linarith [hqi]
      · rw [Function.update_of_ne hki]; exact hq0 k
    · rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
      rw [Finset.sum_erase_eq_sub hgs]
      rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ ({i} : Finset (Fin 2))), Finset.sum_singleton]
      rw [hsat]; ring
    · intro k
      by_cases hki : k = i
      · subst k; rw [Function.update_self, Function.update_self]
        have hvu : vbarSum w p (A i ∪ {g}) = vbarSum w p (A i) + vbarSum w p ({g} : Finset G) :=
          vbarSum_union w p (Finset.disjoint_singleton_right.mpr (hgA i))
        have hvg : vbarSum w p ({g} : Finset G) = max (p g) (w g) := by simp [vbarSum, vbar]
        rw [hvu, hvg]
        have hmax : p g ≤ max (p g) (w g) := le_max_left _ _
        have := hge i
        linarith
      · rw [Function.update_of_ne hki, Function.update_of_ne hki]
        exact hge k
  rcases (show p g ≤ q 0 ∨ p g ≤ q 1 by
      by_contra h; push_neg at h; obtain ⟨h0, h1⟩ := h; linarith [hsumbound, hq01]) with h0 | h1
  · exact key 0 1 (by decide) h0
  · exact key 1 0 (by decide) h1
end FairSelling
