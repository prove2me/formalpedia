-- Prove2me | solution 1 for AvramDividend.Classical.avram_bridge20261123_A77_degenerate_original_physical_poisson_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T15:39:34.947276+00:00
-- url     : https://prove2.me/submissions/a4d76803-e117-4980-b2a0-7e217290ae08

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_negative_borel_count_poisson_law
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top11_original_zero_nu_actual_jumpmark_zero_ae
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0,
        if 0 < u ∧ u ≤ t then
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
        else 0)
    (hDeg : X.ν = 0 ∨ t = 0 ∨ θ = 0) :
    ∃ (N : Ω → ℕ) (r : ℝ≥0) (m : ℝ),
      HasLaw N (poissonMeasure r) P ∧
      (∫ ω, Real.exp (θ * J ω) ∂P) =
        ∫ ω, m ^ (N ω) ∂P ∧
      (r : ℝ) * (m - 1) =
        (t : ℝ) *
          (∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 ∂X.ν) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨N, r, hN, hLaw, hCount, hRate⟩ :=
    AvramDividend.Classical.avram_a20_original_negative_borel_count_poisson_law
      X hFinite t (Iio (0 : ℝ)) measurableSet_Iio (Subset.rfl)
  refine ⟨N, r, (1 : ℝ), hLaw, ?_, ?_⟩
  · have hExpOne :
        ∀ᵐ ω ∂P, Real.exp (θ * J ω) = 1 := by
      rcases hDeg with hNuZero | hRest
      · have hNoJumps :=
          AvramDividend.Classical.avram_ubv_top11_original_zero_nu_actual_jumpmark_zero_ae
            X hNuZero
        filter_upwards [hJEq, hNoJumps] with ω hω hωNoJumps
        have hAllZero :
            (∑' u : ℝ≥0,
              if 0 < u ∧ u ≤ t then
                X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
              else 0) = (0 : ℝ) := by
          have hTermZero (u : ℝ≥0) :
              (if 0 < u ∧ u ≤ t then
                X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
              else 0) = (0 : ℝ) := by
            by_cases hu : 0 < u ∧ u ≤ t
            · simp only [if_pos hu, hωNoJumps u hu.1]
            · simp [hu]
          simp only [hTermZero, tsum_zero]
        rw [hω, hAllZero]
        simp
      · rcases hRest with hTimeZero | hThetaZero
        · filter_upwards [hJEq] with ω hω
          have hAllZero :
              (∑' u : ℝ≥0,
                if 0 < u ∧ u ≤ t then
                  X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
                else 0) = (0 : ℝ) := by
            have hCannot (u : ℝ≥0) : ¬ (0 < u ∧ u ≤ t) := by
              rintro ⟨huPos, huLE⟩
              have huZero : u = 0 := by
                simpa [hTimeZero] using huLE
              exact (ne_of_gt huPos) huZero
            simp [hCannot]
          rw [hω, hAllZero]
          simp
        · filter_upwards [] with ω
          simp [hThetaZero]
    apply integral_congr_ae
    filter_upwards [hExpOne] with ω hω
    simpa only [one_pow] using hω
  · simp only [sub_self, mul_zero]
    rcases hDeg with hNuZero | hRest
    · simp [hNuZero]
    · rcases hRest with hTimeZero | hThetaZero
      · simp [hTimeZero]
      · simp [hThetaZero]
