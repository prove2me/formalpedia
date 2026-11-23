-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.intTwoSided
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:57:31.55481+00:00
-- url     : https://prove2.me/submissions/642a28d9-6c52-4ac8-a90d-2e0f2a3a3256

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_TwoSided
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_mem_box_iff
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_cls_out
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_inv_eq_cls

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
namespace Formalism.DoubleCosetMeasures.P
theorem _root_.solution : Formalism.DoubleCosetMeasures.IntTwoSided := by
  classical
  intro G₁ G₂ _ _ _ _ _ _ _ _ _ _ μ₁ μ₂ _ _ _ _ K₁ K₂ hK₁ hK₂ E _ _ _ f hf hcs
  set g : Quotient (QuotientGroup.rightRel K₁) × (G₂ ⧸ K₂) → E := fun p => f (p.1.out, p.2.out) with hg
  have hopen : ∀ p, IsOpen (box K₁ K₂ p) := fun p =>
    (hK₁.preimage (continuous_mul_right _)).prod (hK₂.preimage (continuous_mul_left _))
  have hmeas : ∀ p, MeasurableSet (box K₁ K₂ p) := fun p =>
    (hK₁.preimage (continuous_mul_right _)).measurableSet.prod
      (hK₂.preimage (continuous_mul_left _)).measurableSet
  have hfg : ∀ z, f z = g (clsTS K₁ K₂ z) := fun z => inv_eq_cls K₁ K₂ f hf z
  have hfin : (Function.support g).Finite := by
    obtain ⟨t, ht⟩ := hcs.elim_finite_subcover (fun p => box K₁ K₂ p) hopen
      (fun z _ => Set.mem_iUnion.2 ⟨clsTS K₁ K₂ z, (mem_box_iff K₁ K₂ _ z).2 rfl⟩)
    refine t.finite_toSet.subset fun p hp => ?_
    have hz : ((p.1.out, p.2.out) : G₁ × G₂) ∈ tsupport f := subset_tsupport f hp
    obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.1 (ht hz)
    have hpi := (mem_box_iff K₁ K₂ i _).1 hzi
    rw [cls_out] at hpi
    rw [hpi]
    exact hi
  refine ⟨hfin, ?_⟩
  change ∫ p, f p ∂(μ₁.prod μ₂) = ∑ᶠ p : Quotient (QuotientGroup.rightRel K₁) × (G₂ ⧸ K₂),
    ((μ₁ (K₁ : Set G₁)).toReal * (μ₂ (K₂ : Set G₂)).toReal) • g p
  set S := hfin.toFinset with hS
  have hsum : ∑ᶠ p : Quotient (QuotientGroup.rightRel K₁) × (G₂ ⧸ K₂),
      ((μ₁ (K₁ : Set G₁)).toReal * (μ₂ (K₂ : Set G₂)).toReal) • g p =
      ∑ p ∈ S, ((μ₁ (K₁ : Set G₁)).toReal * (μ₂ (K₂ : Set G₂)).toReal) • g p := by
    apply finsum_eq_sum_of_support_subset
    intro p hp
    rw [hS, Set.Finite.coe_toFinset]
    intro h
    apply hp
    simp [h]
  rw [hsum]
  have hdecomp : f = fun z => ∑ p ∈ S, (box K₁ K₂ p).indicator (fun _ => g p) z := by
    funext z
    have hind : ∀ p, (box K₁ K₂ p).indicator (fun _ => g p) z =
        if clsTS K₁ K₂ z = p then g p else 0 := by
      intro p
      simp only [Set.indicator, mem_box_iff]
    simp only [hind, Finset.sum_ite_eq]
    rw [hfg z]
    split_ifs with h
    · rfl
    · rw [hS, Set.Finite.mem_toFinset, Function.mem_support, not_not] at h
      exact h
  have hbox : ∀ p, (μ₁.prod μ₂) (box K₁ K₂ p) = μ₁ (K₁ : Set G₁) * μ₂ (K₂ : Set G₂) := by
    intro p
    rw [box, Measure.prod_prod, measure_preimage_mul_right, measure_preimage_mul]
  have hpiece : ∀ p, ∫ z, (box K₁ K₂ p).indicator (fun _ => g p) z ∂(μ₁.prod μ₂) =
      ((μ₁ (K₁ : Set G₁)).toReal * (μ₂ (K₂ : Set G₂)).toReal) • g p := by
    intro p
    rw [integral_indicator_const _ (hmeas p), Measure.real, hbox p, ENNReal.toReal_mul]
  by_cases hint : Integrable f (μ₁.prod μ₂)
  · have hI : ∀ p ∈ S, Integrable ((box K₁ K₂ p).indicator (fun _ => g p)) (μ₁.prod μ₂) := by
      intro p _
      refine (hint.indicator (hmeas p)).congr (Filter.Eventually.of_forall fun z => ?_)
      by_cases hz : z ∈ box K₁ K₂ p
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, hfg z, (mem_box_iff K₁ K₂ p z).1 hz]
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
    conv_lhs => rw [hdecomp]
    rw [integral_finset_sum S hI]
    exact Finset.sum_congr rfl fun p _ => hpiece p
  · rw [integral_undef hint]
    have hex : ∃ p ∈ S, ¬ Integrable ((box K₁ K₂ p).indicator (fun _ => g p)) (μ₁.prod μ₂) := by
      by_contra hne
      push_neg at hne
      apply hint
      rw [hdecomp]
      exact integrable_finset_sum S hne
    obtain ⟨p, -, hnp⟩ := hex
    have htop : μ₁ (K₁ : Set G₁) * μ₂ (K₂ : Set G₂) = ⊤ := by
      by_contra hne
      apply hnp
      rw [integrable_indicator_iff (hmeas p)]
      exact integrableOn_const (by rw [hbox p]; exact hne)
    have h0 : (μ₁ (K₁ : Set G₁)).toReal * (μ₂ (K₂ : Set G₂)).toReal = 0 := by
      rw [← ENNReal.toReal_mul, htop, ENNReal.toReal_top]
    simp [h0]
end Formalism.DoubleCosetMeasures.P
