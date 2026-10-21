-- Prove2me | solution 1 for DelayDep.Equiv.display_after_theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T09:23:19.271556+00:00
-- url     : https://prove2.me/submissions/3dbe7097-514f-4307-b5a8-35776920e977

import Mathlib
import Definitions.Def_DelayDep_Equiv_Model

open MeasureTheory DelayDep.Equiv Function

theorem solution (f : ℝ → ℝ → ℝ) (hf : IsJointPdf f) :
    (∀ x z : ℝ, 0 ≤ x → 0 ≤ z →
      (1 - ∫ u in Set.Icc 0 x, psiEn f u z) * tailT f z =
        ∫ v in Set.Ioi z, ∫ u in Set.Ioi x, f u v) ∧
    (∀ z : ℝ, 0 ≤ z →
      AntitoneOn (fun x => ∫ v in Set.Ioi z, ∫ u in Set.Ioi x, f u v) (Set.Ici 0)) ∧
    (∀ x : ℝ, 0 ≤ x →
      AntitoneOn (fun z => ∫ v in Set.Ioi z, ∫ u in Set.Ioi x, f u v) (Set.Ici 0)) := by
  obtain ⟨hfm, hf0, hf1⟩ := hf
  set μ : Measure ℝ := volume.restrict (Set.Ici 0) with hμ
  have hprod : volume.restrict (Set.Ici (0:ℝ) ×ˢ Set.Ici (0:ℝ)) = μ.prod μ := by
    rw [hμ, Measure.prod_restrict, ← Measure.volume_eq_prod]
  have hI : Integrable (uncurry f) (μ.prod μ) := by
    refine ⟨hfm.aestronglyMeasurable, ?_⟩
    have h0 : 0 ≤ᵐ[μ.prod μ] uncurry f := Filter.Eventually.of_forall (fun p => hf0 p.1 p.2)
    rw [hasFiniteIntegral_iff_ofReal h0, ← hprod]
    have : ∫⁻ a, ENNReal.ofReal (uncurry f a) ∂(volume.restrict (Set.Ici (0:ℝ) ×ˢ Set.Ici (0:ℝ)))
        = 1 := hf1
    rw [this]; exact ENNReal.one_lt_top
  have hIst : ∀ s t : Set ℝ, s ⊆ Set.Ici 0 → t ⊆ Set.Ici 0 →
      Integrable (uncurry f) ((volume.restrict s).prod (volume.restrict t)) := by
    intro s t hs ht
    refine hI.mono_measure ?_
    rw [Measure.prod_restrict, hμ, Measure.prod_restrict]
    exact Measure.restrict_mono (Set.prod_mono hs ht) le_rfl
  have hsec : ∀ᵐ v ∂μ, Integrable (fun u => f u v) μ := hI.prod_left_ae
  have hIoi : ∀ a : ℝ, 0 ≤ a → Set.Ioi a ⊆ Set.Ici 0 := fun a ha y hy => le_trans ha (le_of_lt hy)
  have hIcc : ∀ a : ℝ, Set.Icc 0 a ⊆ Set.Ici 0 := fun a y hy => hy.1
  have hsecν : ∀ z : ℝ, 0 ≤ z → ∀ᵐ v ∂(volume.restrict (Set.Ioi z)), Integrable (fun u => f u v) μ :=
    fun z hz => ae_mono (Measure.restrict_mono (hIoi z hz) le_rfl) hsec
  have hinner_nonneg : ∀ (s : Set ℝ) v, 0 ≤ ∫ u in s, f u v :=
    fun s v => integral_nonneg (fun u => hf0 u v)
  have hinner_nonneg2 : ∀ (s : Set ℝ) u, 0 ≤ ∫ v in s, f u v :=
    fun s u => integral_nonneg (fun v => hf0 u v)
  refine ⟨?_, ?_, ?_⟩
  · intro x z hx hz
    set A := ∫ u in Set.Icc 0 x, ∫ v in Set.Ioi z, f u v with hA
    set B := ∫ v in Set.Ioi z, ∫ u in Set.Ioi x, f u v with hB
    have hkey : tailT f z = A + B := by
      have h1 : tailT f z = ∫ v in Set.Ioi z, ∫ u in Set.Ici 0, f u v := rfl
      have h2 : (∫ v in Set.Ioi z, ∫ u in Set.Ici 0, f u v) =
          ∫ v in Set.Ioi z, ((∫ u in Set.Icc 0 x, f u v) + ∫ u in Set.Ioi x, f u v) := by
        apply integral_congr_ae
        filter_upwards [hsecν z hz] with v hv
        have hv' : IntegrableOn (fun u => f u v) (Set.Ici 0) volume := hv
        rw [← Set.Icc_union_Ioi_eq_Ici hx]
        exact setIntegral_union (Set.disjoint_left.mpr (fun y hy hy' => absurd hy.2 (not_le.mpr hy'))) measurableSet_Ioi
          (hv'.mono_set (hIcc x)) (hv'.mono_set (hIoi x hx))
      have h3 := integral_add (hIst (Set.Icc 0 x) (Set.Ioi z) (hIcc x) (hIoi z hz)).integral_prod_right
        (hIst (Set.Ioi x) (Set.Ioi z) (hIoi x hx) (hIoi z hz)).integral_prod_right
      have h4 : A = ∫ v in Set.Ioi z, ∫ u in Set.Icc 0 x, f u v :=
        integral_integral_swap (f := f) (hIst (Set.Icc 0 x) (Set.Ioi z) (hIcc x) (hIoi z hz))
      rw [h1, h2, h4, hB]
      exact h3
    have hA0 : 0 ≤ A := integral_nonneg (fun u => hinner_nonneg2 _ u)
    have hB0 : 0 ≤ B := integral_nonneg (fun v => hinner_nonneg _ v)
    have hpsi : (∫ u in Set.Icc 0 x, psiEn f u z) = A / tailT f z := by
      unfold psiEn; rw [integral_div]
    rw [hpsi]
    by_cases ht : tailT f z = 0
    · rw [ht, mul_zero]; linarith
    · field_simp; linarith
  · intro z hz a ha b hb hab
    apply integral_mono_ae (hIst (Set.Ioi b) (Set.Ioi z) (hIoi b hb) (hIoi z hz)).integral_prod_right
      (hIst (Set.Ioi a) (Set.Ioi z) (hIoi a ha) (hIoi z hz)).integral_prod_right
    filter_upwards [hsecν z hz] with v hv
    have hv' : IntegrableOn (fun u => f u v) (Set.Ici 0) volume := hv
    exact setIntegral_mono_set (hv'.mono_set (hIoi a ha))
      (Filter.Eventually.of_forall (fun u => hf0 u v)) (Set.Ioi_subset_Ioi hab).eventuallyLE
  · intro x hx a ha b hb hab
    exact setIntegral_mono_set
      (hIst (Set.Ioi x) (Set.Ioi a) (hIoi x hx) (hIoi a ha)).integral_prod_right
      (Filter.Eventually.of_forall (fun v => hinner_nonneg _ v)) (Set.Ioi_subset_Ioi hab).eventuallyLE
