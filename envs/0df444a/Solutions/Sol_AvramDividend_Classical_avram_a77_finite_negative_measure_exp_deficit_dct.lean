-- Prove2me | solution 1 for AvramDividend.Classical.avram_a77_finite_negative_measure_exp_deficit_dct
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T22:31:46.952551+00:00
-- url     : https://prove2.me/submissions/f250d1f8-61ba-4a47-856b-52e781af6e59

/- Original Avram negative Lévy mark intensity exponential deficit
   convergence under finite negative mark measure.
   Independent of any Poisson construction; source-faithful ν. -/
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    (ν : Measure ℝ) (hFinite : ν (Iio (0 : ℝ)) ≠ ⊤)
    (θ : ℝ) (q : ℕ → ℝ → ℝ)
    (hqMeas : ∀ n, Measurable (q n))
    (hqNonpos : ∀ n y, y < 0 → q n y ≤ 0)
    (hLimit : ∀ y, y < 0 →
      Tendsto (fun n => q n y) atTop (𝓝 (θ * y))) :
    Tendsto
      (fun n => ∫ y in Iio (0 : ℝ), Real.exp (q n y) - 1 ∂ν)
      atTop
      (𝓝 (∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 ∂ν)) := by
  haveI hFiniteMeasure :
      IsFiniteMeasure (ν.restrict (Iio (0 : ℝ))) :=
    isFiniteMeasure_restrict.mpr hFinite
  have hMeas : ∀ n,
      AEStronglyMeasurable
        (fun y : ℝ => Real.exp (q n y) - 1)
        (ν.restrict (Iio (0 : ℝ))) := by
    intro n
    exact ((hqMeas n).exp.sub measurable_const).aestronglyMeasurable
  have hBound : ∀ n,
      ∀ᵐ y ∂ν.restrict (Iio (0 : ℝ)),
        ‖Real.exp (q n y) - 1‖ ≤ (1 : ℝ) := by
    intro n
    filter_upwards [ae_restrict_mem (measurableSet_Iio)] with y hy
    have he : Real.exp (q n y) ≤ 1 :=
      Real.exp_le_one_iff.mpr (hqNonpos n y hy)
    have hp : 0 < Real.exp (q n y) := Real.exp_pos _
    change |Real.exp (q n y) - 1| ≤ (1 : ℝ)
    rw [abs_of_nonpos (sub_nonpos.mpr he)]
    linarith
  have hTendsto :
      ∀ᵐ y ∂ν.restrict (Iio (0 : ℝ)),
        Tendsto (fun n => Real.exp (q n y) - 1)
          atTop (𝓝 (Real.exp (θ * y) - 1)) := by
    filter_upwards [ae_restrict_mem (measurableSet_Iio)] with y hy
    exact ((Real.continuous_exp.tendsto _).comp (hLimit y hy)).sub
      tendsto_const_nhds
  exact tendsto_integral_of_dominated_convergence
    (fun _ : ℝ => (1 : ℝ)) hMeas
    (integrable_const _) hBound hTendsto

