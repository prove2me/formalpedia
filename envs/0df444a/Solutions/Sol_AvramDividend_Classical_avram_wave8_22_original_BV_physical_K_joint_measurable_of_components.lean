-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_22_original_BV_physical_K_joint_measurable_of_components
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:00:20.355611+00:00
-- url     : https://prove2.me/submissions/914236a3-82b7-494c-af62-030b03d257fe

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Joint measurability of the original BV physical drift, Lévy jump and discount integrand on the controlled left-limit path. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕)
  (q : ℝ) (w : ℝ → ℝ) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
  (K : ℝ≥0 → Ω → ℝ)
  (hK : ∀ t ω, K t ω =
    Real.exp (-(q * (t : ℝ))) *
      (X.drift * deriv w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) +
      (∫ z in Iio (0 : ℝ),
        w (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s ω - rightLimit D s ω) t + z) -
        w (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s ω - rightLimit D s ω) t) ∂X.ν) -
      q * w (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω) t)))
  (hYmeas : Measurable (fun p : ℝ≥0 × Ω =>
    Function.leftLim (fun s : ℝ≥0 =>
      x + X.X s p.2 - rightLimit D s p.2) p.1))
  (hDerivMeas : Measurable (deriv w))
  (hWMeas : Measurable w)
  (hJMeas : Measurable (fun y : ℝ =>
    ∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν)) :
  Measurable (fun p : ℝ≥0 × Ω => K p.1 p.2) := by
  let Y : (ℝ≥0 × Ω) → ℝ := fun p =>
    Function.leftLim (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  have hy : Measurable Y := hYmeas
  have hd : Measurable (fun p => deriv w (Y p)) := hDerivMeas.comp hy
  have hw : Measurable (fun p => w (Y p)) := hWMeas.comp hy
  have hj : Measurable (fun p =>
      ∫ z in Iio (0 : ℝ), w (Y p + z) - w (Y p) ∂X.ν) :=
    hJMeas.comp hy
  have hb : Measurable (fun p =>
      X.drift * deriv w (Y p) +
      (∫ z in Iio (0 : ℝ), w (Y p + z) - w (Y p) ∂X.ν) - q * w (Y p)) :=
    ((measurable_const.mul hd).add hj).sub (measurable_const.mul hw)
  have ht : Measurable (fun p : ℝ≥0 × Ω => (p.1 : ℝ)) :=
    measurable_coe_nnreal_real.comp measurable_fst
  have he : Measurable (fun p : ℝ≥0 × Ω => Real.exp (-(q * (p.1 : ℝ)))) :=
    Real.measurable_exp.comp ((measurable_const.mul ht).neg)
  have hp : Measurable (fun p : ℝ≥0 × Ω =>
      Real.exp (-(q * (p.1 : ℝ))) *
        (X.drift * deriv w (Y p) +
        (∫ z in Iio (0 : ℝ), w (Y p + z) - w (Y p) ∂X.ν) -
        q * w (Y p))) := he.mul hb
  have hKeq :
      (fun p : ℝ≥0 × Ω => K p.1 p.2) =
      (fun p : ℝ≥0 × Ω => Real.exp (-(q * (p.1 : ℝ))) *
        (X.drift * deriv w (Y p) +
        (∫ z in Iio (0 : ℝ), w (Y p + z) - w (Y p) ∂X.ν) -
        q * w (Y p))) := by
    funext p
    exact hK p.1 p.2
  rw [hKeq]
  exact hp
