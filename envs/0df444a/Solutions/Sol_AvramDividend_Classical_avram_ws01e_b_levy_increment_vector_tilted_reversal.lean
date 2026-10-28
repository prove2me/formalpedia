-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_levy_increment_vector_tilted_reversal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T07:49:07.877144+00:00
-- url     : https://prove2.me/submissions/de572a98-73d5-4e3e-8f9c-6ccf4cd50631

import Mathlib
import Theorems.Thm_AvramDividend_Classical_levy_equal_mesh_increment_vector_law_reversal_ws01e_b
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_withDensity_preserves_measurable_symmetry

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (δ : ℝ≥0) (n : ℕ)
    (w : (Fin n → ℝ) → ℝ≥0∞) (hw : Measurable w)
    (hwR : ∀ v : Fin n → ℝ, w (fun i => v i.rev) = w v)
    (A : Set (Fin n → ℝ)) (hA : MeasurableSet A) :
    ((Measure.map (fun ω : Ω => fun i : Fin n =>
      X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
      X.X ((i.val : ℝ≥0) * δ) ω) P).withDensity w)
      {v : Fin n → ℝ | (fun i => v i.rev) ∈ A} =
    ((Measure.map (fun ω : Ω => fun i : Fin n =>
      X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
      X.X ((i.val : ℝ≥0) * δ) ω) P).withDensity w) A := by
  let inc : Ω → (Fin n → ℝ) := fun ω i =>
    X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
    X.X ((i.val : ℝ≥0) * δ) ω
  let R : (Fin n → ℝ) → (Fin n → ℝ) := fun v i => v i.rev
  have hm : Measurable inc := by
    apply measurable_pi_lambda
    intro i
    exact (X.adapted.measurable).sub (X.adapted.measurable)
  have hR : Measurable R := by
    apply measurable_pi_lambda
    intro i
    exact measurable_pi_apply i.rev
  have hSym : Measure.map R (Measure.map inc P) =
      Measure.map inc P := by
    calc
      Measure.map R (Measure.map inc P) =
          Measure.map (R ∘ inc) P := Measure.map_map hR hm
      _ = Measure.map inc P := by
        simpa only [Function.comp_def, R, inc] using
          (levy_equal_mesh_increment_vector_law_reversal_ws01e_b X δ n).symm
  exact avram_ws01e_b_withDensity_preserves_measurable_symmetry
    (Measure.map inc P) R hR hSym w hw hwR A hA
