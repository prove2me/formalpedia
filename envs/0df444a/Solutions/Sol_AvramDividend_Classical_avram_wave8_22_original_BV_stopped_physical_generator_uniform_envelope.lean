-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_22_original_BV_stopped_physical_generator_uniform_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:28:53.132727+00:00
-- url     : https://prove2.me/submissions/580cf79b-a70e-4799-9a2b-238157297ee8

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Order.LeftRightLim
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_discounted_physical_generator_uniform_bound
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- The original stopped BV physical generator is uniformly bounded once its true derivative, ν-kernel and value are controlled. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
  (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ) (x : ℝ)
  (D : ℝ≥0 → Ω → ℝ) (A : Ω → Set ℝ≥0)
  (Y : (ℝ≥0 × Ω) → ℝ)
  (hY : ∀ p, Y p = Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1)
  (K : ℝ≥0 → Ω → ℝ)
  (hK : ∀ p : ℝ≥0 × Ω, K p.1 p.2 =
    Real.exp (-(q * (p.1 : ℝ))) *
      (X.drift * deriv w (Y p) +
      (∫ z in Iio (0 : ℝ), w (Y p + z) - w (Y p) ∂X.ν) -
      q * w (Y p)))
  (F : (ℝ≥0 × Ω) → ℝ)
  (hF : ∀ p, F p = if p.1 ∈ A p.2 then K p.1 p.2 else 0)
  (L M R : ℝ) (hL : 0 ≤ L) (hM : 0 ≤ M) (hR : 0 ≤ R)
  (hBounds : ∀ p : ℝ≥0 × Ω, p.1 ∈ A p.2 →
    |deriv w (Y p)| ≤ L ∧
    |∫ z in Iio (0 : ℝ), w (Y p + z) - w (Y p) ∂X.ν| ≤ M ∧
    |w (Y p)| ≤ R) :
  0 ≤ |X.drift| * L + M + |q| * R ∧
  ∀ p : ℝ≥0 × Ω, ‖F p‖ ≤ |X.drift| * L + M + |q| * R := by
  have hB : 0 ≤ |X.drift| * L + M + |q| * R := by positivity
  refine ⟨hB, ?_⟩
  intro p
  by_cases hp : p.1 ∈ A p.2
  · obtain ⟨hd, hj, hw⟩ := hBounds p hp
    have hi := (avram_wave8_22_original_BV_discounted_physical_generator_uniform_bound
      X hBV q hq w p.1 (Y p) L M R hL hM hR hd hj hw).2
    rw [hF p, if_pos hp, hK p]
    simpa [Real.norm_eq_abs] using hi
  · rw [hF p, if_neg hp]
    simpa using hB
