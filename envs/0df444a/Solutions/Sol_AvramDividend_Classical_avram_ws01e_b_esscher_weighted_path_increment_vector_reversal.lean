-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_esscher_weighted_path_increment_vector_reversal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T08:45:26.036588+00:00
-- url     : https://prove2.me/submissions/86a37977-4c0b-4558-bf4a-f99ed733c4a3

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_map_withDensity_observable_density
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_esscher_grid_increment_vector_reversal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Finset Set
open scoped NNReal ENNReal BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (δ : ℝ≥0) (n : ℕ) (θ : ℝ)
    (A : Set (Fin n → ℝ)) (hA : MeasurableSet A) :
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * (∑ i : Fin n,
        (X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
         X.X ((i.val : ℝ≥0) * δ) ω)) -
        (((n : ℝ≥0) * δ : ℝ≥0) : ℝ) * X.ψ θ))))
      {ω : Ω | (fun i : Fin n =>
        X.X (((i.rev.val + 1 : ℕ) : ℝ≥0) * δ) ω -
        X.X ((i.rev.val : ℝ≥0) * δ) ω) ∈ A} =
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * (∑ i : Fin n,
        (X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
         X.X ((i.val : ℝ≥0) * δ) ω)) -
        (((n : ℝ≥0) * δ : ℝ≥0) : ℝ) * X.ψ θ))))
      {ω : Ω | (fun i : Fin n =>
        X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
        X.X ((i.val : ℝ≥0) * δ) ω) ∈ A} := by
  let F : Ω → (Fin n → ℝ) := fun ω i =>
    X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
      X.X ((i.val : ℝ≥0) * δ) ω
  let R : (Fin n → ℝ) → (Fin n → ℝ) := fun v i => v i.rev
  let w : (Fin n → ℝ) → ℝ≥0∞ := fun v =>
    ENNReal.ofReal
      (Real.exp (θ * (∑ i : Fin n, v i) -
        (((n : ℝ≥0) * δ : ℝ≥0) : ℝ) * X.ψ θ))
  have hF : Measurable F := by
    apply measurable_pi_lambda
    intro i
    exact (X.adapted.measurable).sub (X.adapted.measurable)
  have hw : Measurable w := by
    dsimp [w]
    fun_prop
  have hR : Measurable R := by
    apply measurable_pi_lambda
    intro i
    exact measurable_pi_apply i.rev
  have hPush := avram_ws01e_b_map_withDensity_observable_density
    P F hF w hw
  have hSym := avram_ws01e_b_esscher_grid_increment_vector_reversal
    X δ n θ A hA
  change ((Measure.map F P).withDensity w) (R ⁻¹' A) =
    ((Measure.map F P).withDensity w) A at hSym
  rw [← hPush, Measure.map_apply hF (hA.preimage hR),
    Measure.map_apply hF hA] at hSym
  simpa only [F, R, w, Function.comp_def, Set.preimage, Set.mem_setOf_eq]
    using hSym
