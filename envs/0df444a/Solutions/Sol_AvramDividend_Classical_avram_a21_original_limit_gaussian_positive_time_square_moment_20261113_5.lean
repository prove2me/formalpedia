-- Prove2me | solution 5 for AvramDividend.Classical.avram_a21_original_limit_gaussian_positive_time_square_moment_20261113
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:06:25.507362+00:00
-- url     : https://prove2.me/submissions/e1189d36-381b-4624-81ba-c9cfb32c0ec3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_sigma_zero_gaussian_residual_limit_ae_zero_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a29_original_positive_sigma_gaussian_intrinsic_exact_haslaw
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The intrinsic Gaussian second moment follows from original exact law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω)
        atTop (nhds (R T ω))) :
    ∀ t : ℝ≥0, 0 < t →
      Integrable (fun ω => (R t ω) ^ 2) P ∧
      (∫ ω, (R t ω) ^ 2 ∂P) = (t : ℝ) * X.σ ^ 2 := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro t ht
  by_cases hs : X.σ = 0
  · have hZero :=
      avram_a21_original_sigma_zero_gaussian_residual_limit_ae_zero_20261113
        X hX hFinite R hR hs
    have hEq : (fun ω => (R t ω) ^ 2) =ᵐ[P] (fun _ => (0 : ℝ)) := by
      filter_upwards [hZero] with ω hz
      simp [hz t]
    constructor
    · exact (integrable_const (0 : ℝ) : Integrable (fun _ : Ω => (0 : ℝ)) P).congr hEq.symm
    · calc
        (∫ ω, (R t ω) ^ 2 ∂P) = ∫ ω, (0 : ℝ) ∂P :=
          integral_congr_ae hEq
        _ = (t : ℝ) * X.σ ^ 2 := by simp [hs]
  · have hp : 0 < X.σ := lt_of_le_of_ne X.σ_nonneg (Ne.symm hs)
    have hEq : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, R u ω = R u ω :=
      Filter.Eventually.of_forall (fun _ _ => rfl)
    let v : ℝ≥0 := NNReal.mk ((t : ℝ) * X.σ ^ 2)
      (mul_nonneg (NNReal.coe_nonneg t) (sq_nonneg X.σ))
    have hLaw : HasLaw (R t) (gaussianReal 0 v) P :=
      avram_a29_original_positive_sigma_gaussian_intrinsic_exact_haslaw
        X hX hFinite hp R hR R hEq t
    have hLp : MemLp (fun x : ℝ => x) 2 (gaussianReal 0 v) :=
      memLp_id_gaussianReal 2
    have hSquareInt : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) :=
      (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mp hLp
    have hSquareVar :
        Var[(fun x : ℝ => x); gaussianReal (0 : ℝ) v] = (v : ℝ) :=
      variance_fun_id_gaussianReal
    rw [variance_eq_integral (X := (fun x : ℝ => x)) (μ := gaussianReal (0 : ℝ) v) measurable_id'.aemeasurable] at hSquareVar
    simp [id, integral_id_gaussianReal] at hSquareVar
    have hSquare : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) ∧
        (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v) = (v : ℝ) :=
      ⟨hSquareInt, hSquareVar⟩
    have hAS : AEStronglyMeasurable
        (fun x : ℝ => x ^ 2) (P.map (R t)) := by fun_prop
    have hInt : Integrable (fun ω => (R t ω) ^ 2) P := by
      have h := (integrable_map_measure hAS hLaw.aemeasurable).mp
        (by rw [hLaw.map_eq]; exact hSquare.1)
      simpa only [Function.comp_def] using h
    refine ⟨hInt, ?_⟩
    have hAS' : AEStronglyMeasurable
        (fun x : ℝ => x ^ 2) (gaussianReal 0 v) := by fun_prop
    calc
      (∫ ω, (R t ω) ^ 2 ∂P) =
          (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v) := by
        simpa only [Function.comp_def] using hLaw.integral_comp hAS'
      _ = (v : ℝ) := hSquare.2
      _ = (t : ℝ) * X.σ ^ 2 := rfl
