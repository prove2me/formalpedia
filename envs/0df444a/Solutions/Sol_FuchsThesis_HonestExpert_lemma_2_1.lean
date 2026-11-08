-- Prove2me | solution 1 for FuchsThesis.HonestExpert.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:16:41.914279+00:00
-- url     : https://prove2.me/submissions/a094d60b-be0f-40e7-b6eb-baa6f582568a

import Mathlib

open MeasureTheory

theorem solution {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : MonotoneOn f (Set.Icc a b)) :
    (∀ᵐ x ∂(volume.restrict (Set.Icc a b)), DifferentiableAt ℝ f x) ∧
      Measurable (deriv f) ∧
      IntervalIntegrable (deriv f) volume a b ∧
      ∫ x in a..b, deriv f x ≤ f b - f a := by
  have hf' : MonotoneOn f (Set.uIcc a b) := by rwa [Set.uIcc_of_le hab]
  refine ⟨?_, measurable_deriv f, hf'.intervalIntegrable_deriv, ?_⟩
  · rw [← Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := volume))]
    have h1 := (hf.mono Set.Ioo_subset_Icc_self).ae_differentiableWithinAt measurableSet_Ioo
    filter_upwards [h1, ae_restrict_mem measurableSet_Ioo] with x hx1 hx2
    exact hx1.differentiableAt (Ioo_mem_nhds hx2.1 hx2.2)
  · have h := hf'.intervalIntegral_deriv_mem_uIcc
    have hle : f a ≤ f b := hf ⟨le_refl a, hab⟩ ⟨hab, le_refl b⟩ hab
    rw [Set.uIcc_of_le (by linarith)] at h
    exact h.2
