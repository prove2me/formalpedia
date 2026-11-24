-- Prove2me | solution 1 for FairSelling.EqualProceedsBagFilling.exists_equalProceeds_TPS_approx_full
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:55:59.332921+00:00
-- url     : https://prove2.me/submissions/9c1709e4-5547-423e-8826-1ba3df69bac0

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_EqualProceedsBagFilling
import Theorems.Thm_FairSelling_EqualProceedsBagFilling_exists_equalProceeds_TPS_approx

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.EqualProceedsBagFilling
variable {G : Type*} {n : ℕ}
variable {vi p : G → ℝ} {tk : ℝ}
variable [Fintype G] [DecidableEq G]
namespace FairSelling.EqualProceedsBagFilling
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g) :
    ∃ o : Outcome G n, o.Valid p ∧ o.EqualProceeds p ∧
      o.sold ∪ Finset.univ.biUnion o.kept = Finset.univ ∧
      (∑ j, o.money j) = ∑ g ∈ o.sold, p g ∧
      ∀ i, TPS n (v i) p / n ≤ util (v i) o i := by
  classical
  obtain ⟨o, hvalid, hep, hsat⟩ := exists_equalProceeds_TPS_approx v p hn hv hp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set i0 : Fin n := ⟨0, hn⟩ with hi0
  set L : Finset G := Finset.univ \ (o.sold ∪ Finset.univ.biUnion o.kept) with hL
  set kept' : Fin n → Finset G := Function.update o.kept i0 (o.kept i0 ∪ L) with hkept'
  have hLsold : Disjoint L o.sold :=
    Finset.disjoint_left.mpr fun g hg hg' =>
      (Finset.mem_sdiff.mp hg).2 (Finset.mem_union_left _ hg')
  have hLkept : ∀ k, Disjoint L (o.kept k) := fun k =>
    Finset.disjoint_left.mpr fun g hg hg' =>
      (Finset.mem_sdiff.mp hg).2
        (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hg'⟩))
  have hkeptsub : ∀ k, o.kept k ⊆ kept' k := by
    intro k
    by_cases hk : k = i0
    · subst hk
      simp only [hkept', Function.update_self]
      exact Finset.subset_union_left
    · simp only [hkept', Function.update_of_ne hk]
      exact Finset.Subset.refl _
  have hmem : ∀ k g, g ∈ kept' k → g ∈ o.kept k ∨ g ∈ L := by
    intro k g hg
    by_cases hk : k = i0
    · subst hk
      simp only [hkept', Function.update_self] at hg
      exact Finset.mem_union.mp hg
    · simp only [hkept', Function.update_of_ne hk] at hg
      exact Or.inl hg
  refine ⟨⟨o.sold, kept', o.money⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro j
    refine Finset.disjoint_left.mpr fun g hg hg' => ?_
    rcases hmem j g hg' with h | h
    · exact Finset.disjoint_left.mp (hvalid.1 j) hg h
    · exact Finset.disjoint_left.mp hLsold h hg
  · intro j k hjk
    refine Finset.disjoint_left.mpr fun g hg hg' => ?_
    rcases hmem j g hg with h | h <;> rcases hmem k g hg' with h' | h'
    · exact Finset.disjoint_left.mp (hvalid.2.1 j k hjk) h h'
    · exact Finset.disjoint_left.mp (hLkept j) h' h
    · exact Finset.disjoint_left.mp (hLkept k) h h'
    · -- `g` cannot lie in `L` twice in disjoint bundles; here both bundles contain `L`
      -- which forces `j = k`, contradicting `hjk`
      exfalso
      by_cases hj : j = i0
      · by_cases hk : k = i0
        · exact hjk (hj.trans hk.symm)
        · simp only [hkept', Function.update_of_ne hk] at hg'
          exact Finset.disjoint_left.mp (hLkept k) h' hg'
      · simp only [hkept', Function.update_of_ne hj] at hg
        exact Finset.disjoint_left.mp (hLkept j) h hg
  · exact hvalid.2.2.1
  · exact hvalid.2.2.2
  · exact hep
  · -- every good is sold or allocated
    refine Finset.eq_univ_iff_forall.mpr fun g => ?_
    by_cases hg : g ∈ o.sold ∪ Finset.univ.biUnion o.kept
    · rcases Finset.mem_union.mp hg with h | h
      · exact Finset.mem_union_left _ h
      · obtain ⟨k, -, hk⟩ := Finset.mem_biUnion.mp h
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _,
          hkeptsub k hk⟩)
    · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i0, Finset.mem_univ _, ?_⟩)
      simp only [hkept', Function.update_self]
      exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hg⟩)
  · -- the distributed proceeds are exactly the proceeds of the sold goods
    have h : ∀ j, o.money j = (∑ g ∈ o.sold, p g) / n := hep
    rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_div_cancel₀ _ (ne_of_gt hn')]
  · intro i
    refine le_trans (hsat i) ?_
    unfold util
    have : ∑ g ∈ o.kept i, v i g ≤ ∑ g ∈ kept' i, v i g :=
      Finset.sum_le_sum_of_subset_of_nonneg (hkeptsub i) fun g _ _ => hv i g
    simpa using this
end FairSelling.EqualProceedsBagFilling
