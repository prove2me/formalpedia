-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_h_gaussian_original_nu_quadratic_real_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:33:35.881448+00:00
-- url     : https://prove2.me/submissions/265b6867-c8a5-4fd4-9a40-cef12283751a

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
/-- Original small-negative-jump quadratic energy is a genuine real integral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ) :
    IntegrableOn (fun z : ℝ => z ^ 2)
      (Ioc (-(1 / ((n : ℝ) + 1))) (0 : ℝ)) X.ν ∧
    ENNReal.ofReal (∫ z in Ioc (-(1 / ((n : ℝ) + 1))) (0 : ℝ), z ^ 2 ∂X.ν) =
      ∫⁻ z in Ioc (-(1 / ((n : ℝ) + 1))) (0 : ℝ),
        ENNReal.ofReal (z ^ 2) ∂X.ν := by
  let C : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) 0
  let g : ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (z ^ 2)
  let b : ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (min (1 : ℝ) (z ^ 2))
  have hPoint : ∀ z : ℝ, (C.indicator g) z ≤ b z := by
    intro z
    by_cases hz : z ∈ C
    · have hp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hn : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
      have hd : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 :=
        (div_le_iff₀ hp).2 (by nlinarith [hn])
      have hzl : -1 ≤ z := by
        have hl := hz.1
        dsimp [C] at hz
        linarith
      have hzu : z ≤ 0 := hz.2
      have hmul : 0 ≤ (z + 1) * (-z) := mul_nonneg (by linarith) (by linarith)
      have hsq : z ^ 2 ≤ (1 : ℝ) := by nlinarith [hmul]
      dsimp [g, b]
      rw [Set.indicator_of_mem hz, min_eq_right hsq]
    · dsimp [g, b]
      simp [Set.indicator_of_notMem hz]
  have hLinFin : (∫⁻ z in C, g z ∂X.ν) < ⊤ := by
    calc
      _ = ∫⁻ z, C.indicator g z ∂X.ν :=
        (lintegral_indicator (by dsimp [C]; exact measurableSet_Ioc) g).symm
      _ ≤ ∫⁻ z, b z ∂X.ν :=
        lintegral_mono hPoint
      _ < ⊤ := X.ν_integrable
  have hNN : 0 ≤ᵐ[X.ν.restrict C] (fun z : ℝ => z ^ 2) :=
    Filter.Eventually.of_forall (fun z => sq_nonneg z)
  have hFin : HasFiniteIntegral (fun z : ℝ => z ^ 2) (X.ν.restrict C) :=
    (hasFiniteIntegral_iff_ofReal hNN).2 hLinFin
  have hI : Integrable (fun z : ℝ => z ^ 2) (X.ν.restrict C) :=
    ⟨(measurable_id.pow_const 2).aestronglyMeasurable, hFin⟩
  constructor
  · change Integrable (fun z : ℝ => z ^ 2) (X.ν.restrict C)
    exact hI
  · simpa only [C] using (ofReal_integral_eq_lintegral_ofReal hI hNN)
