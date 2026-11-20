-- Prove2me | solution 1 for DeletionCode.CatalogueAlgebra.new_relation_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:28:08.178934+00:00
-- url     : https://prove2.me/submissions/29a91331-18ca-4d37-9827-c0635bf26810

import Definitions.Def_DeletionCode_RelationSavings
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Definitions.Def_DeletionCode_CatalogueAlgebra
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_injective
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_zero
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_neg
import Theorems.Thm_DeletionCode_CatalogueAlgebra_catalogue_signed_unit
import Theorems.Thm_DeletionCode_CatalogueAlgebra_catalogue_nonzero
import Theorems.Thm_DeletionCode_ComponentFibers_mem_fiber
import Theorems.Thm_DeletionCode_ConnectedBlocks_RuleAdjacent_symm
import Theorems.Thm_DeletionCode_SupportInclusion_supportComponentMap_mk
import Theorems.Thm_DeletionCode_WitnessAlgebra_scalar_multiple_eq_or_neg
attribute [local simp] DeletionCode.ComponentFibers.mem_fiber
attribute [local simp] DeletionCode.SupportInclusion.supportComponentMap_mk


attribute [local simp] DeletionCode.CatalogueAlgebra.rational_zero
attribute [local simp] DeletionCode.CatalogueAlgebra.rational_neg

set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueAlgebra
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks CatalogueBridge
open scoped BigOperators
namespace DeletionCode.CatalogueAlgebra
theorem _root_.solution {t k : ℕ} (ht : 1 ≤ t) (G : RuleSet k)
    (hcat : ∀ u ∈ G, CatalogueRule t k u)
    (w : Gram (windowLength k) → ℤ) (hw : CatalogueRule t k w)
    (hnew : ∀ u ∈ G, w ≠ u ∧ w ≠ -u)
    (hspan : rational w ∈ Submodule.span ℚ (rational '' (↑G : Set _))) :
    ∃ I : RuleSet k, I ⊆ G ∧ 2 ≤ I.card ∧
      ∃ a : (Gram (windowLength k) → ℤ) → ℚ,
        (∀ u ∈ I, a u ≠ 0) ∧
        ∀ g, (w g : ℚ) = ∑ u ∈ I, a u * (u g : ℚ) := by
  classical
  obtain ⟨a, hsum⟩ := (Submodule.mem_span_image_finset_iff_exists_fun' ℚ).mp hspan
  let I := G.filter (fun u => a u ≠ 0)
  have hIG : I ⊆ G := Finset.filter_subset _ _
  have ha : ∀ u ∈ I, a u ≠ 0 := fun u hu => (Finset.mem_filter.mp hu).2
  have hrel : ∀ g, (w g : ℚ) = ∑ u ∈ I, a u * (u g : ℚ) := by
    intro g
    have h := congrFun hsum g
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, rational] at h
    rw [← h]
    symm
    apply Finset.sum_subset hIG
    intro u huG huI
    have hz : a u = 0 := by
      by_contra hne
      exact huI (Finset.mem_filter.mpr ⟨huG, hne⟩)
    simp [hz]
  have hcard : 2 ≤ I.card := by
    by_contra hnot
    have hsmall : I.card ≤ 1 := by omega
    by_cases hzero : I.card = 0
    · have hIempty := Finset.card_eq_zero.mp hzero
      have hwzero : w = 0 := by
        funext g
        have h := hrel g
        simp only [hIempty, Finset.sum_empty] at h
        exact_mod_cast h
      exact catalogue_nonzero ht w hw hwzero
    · have hone : I.card = 1 := by omega
      obtain ⟨u, hI⟩ := Finset.card_eq_one.mp hone
      have huI : u ∈ I := by rw [hI]; exact Finset.mem_singleton_self u
      have huG := hIG huI
      have hlinear : rational w = a u • rational u := by
        funext g
        simpa only [hI, Finset.sum_singleton, rational, Pi.smul_apply, smul_eq_mul]
          using hrel g
      have hu0 : rational u ≠ 0 := by
        intro hu0
        apply catalogue_nonzero ht u (hcat u huG)
        exact rational_injective (hu0.trans rational_zero.symm)
      rcases WitnessAlgebra.scalar_multiple_eq_or_neg (rational u) (rational w) (a u)
        (catalogue_signed_unit u (hcat u huG)) (catalogue_signed_unit w hw)
        hu0 (ha u huI) hlinear with heq | heq
      · exact (hnew u huG).1 (rational_injective heq)
      · exact (hnew u huG).2 (rational_injective (heq.trans (rational_neg u).symm))
  exact ⟨I, hIG, hcard, a, ha, hrel⟩
end DeletionCode.CatalogueAlgebra
