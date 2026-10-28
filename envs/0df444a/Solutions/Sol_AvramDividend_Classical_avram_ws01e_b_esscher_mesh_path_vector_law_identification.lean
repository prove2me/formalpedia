-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_esscher_mesh_path_vector_law_identification
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T08:10:36.988056+00:00
-- url     : https://prove2.me/submissions/accf49ff-801c-4f32-a569-9ced4453e9e8

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_map_withDensity_observable_density
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_equal_mesh_increment_sum_telescopes

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Finset
open scoped NNReal ENNReal BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (δ : ℝ≥0) (n : ℕ) (θ : ℝ) :
    Measure.map
      (fun ω : Ω => fun i : Fin n =>
        X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
        X.X ((i.val : ℝ≥0) * δ) ω)
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * (X.X ((n : ℝ≥0) * δ) ω - X.X 0 ω) -
          (((n : ℝ≥0) * δ : ℝ≥0) : ℝ) * X.ψ θ)))) =
    (Measure.map (fun ω : Ω => fun i : Fin n =>
        X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
        X.X ((i.val : ℝ≥0) * δ) ω) P).withDensity
      (fun v : Fin n → ℝ => ENNReal.ofReal
        (Real.exp (θ * (∑ i : Fin n, v i) -
          (((n : ℝ≥0) * δ : ℝ≥0) : ℝ) * X.ψ θ))) := by
  let inc : Ω → (Fin n → ℝ) := fun ω i =>
    X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
    X.X ((i.val : ℝ≥0) * δ) ω
  let w : (Fin n → ℝ) → ℝ≥0∞ := fun v =>
    ENNReal.ofReal (Real.exp (θ * (∑ i : Fin n, v i) -
      (((n : ℝ≥0) * δ : ℝ≥0) : ℝ) * X.ψ θ))
  have hm : Measurable inc := by
    apply measurable_pi_lambda
    intro i
    exact (X.adapted.measurable).sub (X.adapted.measurable)
  have hSum : Measurable (fun v : Fin n → ℝ => ∑ i : Fin n, v i) :=
    Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)
  have hw : Measurable w := by
    dsimp [w]
    fun_prop
  have hSumPath (ω : Ω) :
      (∑ i : Fin n, inc ω i) =
        X.X ((n : ℝ≥0) * δ) ω - X.X 0 ω := by
    calc
      (∑ i : Fin n, inc ω i) =
        Finset.sum (Finset.range n) (fun j =>
          X.X (((j + 1 : ℕ) : ℝ≥0) * δ) ω -
          X.X ((j : ℝ≥0) * δ) ω) := by
            simpa only [inc] using
              (Fin.sum_univ_eq_sum_range
                (fun j : ℕ => X.X (((j + 1 : ℕ) : ℝ≥0) * δ) ω -
                  X.X ((j : ℝ≥0) * δ) ω) n)
      _ = _ := avram_ws01e_b_equal_mesh_increment_sum_telescopes X δ n ω
  have hWeight : (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * (X.X ((n : ℝ≥0) * δ) ω - X.X 0 ω) -
          (((n : ℝ≥0) * δ : ℝ≥0) : ℝ) * X.ψ θ))) = w ∘ inc := by
    funext ω
    simp only [Function.comp_apply, w, hSumPath ω]
  rw [hWeight]
  exact avram_ws01e_b_map_withDensity_observable_density P inc hm w hw
