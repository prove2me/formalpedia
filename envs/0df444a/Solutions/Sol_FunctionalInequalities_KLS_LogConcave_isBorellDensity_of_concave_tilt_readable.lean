-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.isBorellDensity_of_concave_tilt_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:29:16.062395+00:00
-- url     : https://prove2.me/submissions/50e4f9cf-4b53-4805-a5fc-c9a46f8f2d6f

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_ConcaveTilt
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_integrable_exp_neg_of_eq_tilted_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_rpow_mul_rpow_le_of_convexOn_readable

noncomputable section
open MeasureTheory Set Filter Topology FunctionalInequalities
private theorem FunctionalInequalities.KLS.LogConcave.upperSemicontinuous_mul_positive {E : Type*} [TopologicalSpace E] {f g : E → ℝ}
    (hf : UpperSemicontinuous f) (hg : Continuous g) (hgpos : ∀ y, 0 < g y) :
    UpperSemicontinuous (fun y => f y * g y) := by
  intro y c hc
  obtain ⟨a, ha, hac⟩ := exists_between hc
  have hfu : f y < a / g y := (lt_div_iff₀ (hgpos y)).2 ha
  have htc : a / g y * g y < c := by
    simpa only [div_mul_cancel₀ a (hgpos y).ne'] using hac
  have hgc : ∀ᶠ z in 𝓝 y, a / g y * g z < c :=
    (hg.const_mul (a / g y)).continuousAt.eventually (isOpen_Iio.mem_nhds htc)
  filter_upwards [hf y _ hfu, hgc] with z hz hgz
  exact (mul_le_mul_of_nonneg_right hz.le (hgpos z).le).trans_lt hgz
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [FiniteDimensional ℝ E] in
/-- A continuous concave tilt of a Borell density is a Borell density (zeros of the density allowed). -/
theorem solution (μ ν : ProbabilityMeasure E)
    (m : Measure E) {ρ : E → ℝ} (hρ : FunctionalInequalities.KLS.IsBorellDensity (μ : Measure E) m ρ)
    (φ : E → ℝ) (hφ : Continuous φ) (hconc : ConcaveOn ℝ univ φ)
    (hν : (ν : Measure E) = (μ : Measure E).tilted φ) :
    FunctionalInequalities.KLS.IsBorellDensity (ν : Measure E) m
      (fun x => ρ x * (Real.exp (φ x) / ∫ y, Real.exp (φ y) ∂(μ : Measure E))) := by
  have hi : Integrable (fun x => Real.exp (φ x)) (μ : Measure E) := by
    have h := FunctionalInequalities.KLS.LogConcave.integrable_exp_neg_of_eq_tilted_readable
      (ν := ν) (m := (μ : Measure E)) (W := -φ) (by simpa using hν)
    simpa using h
  let Z : ℝ := ∫ y, Real.exp (φ y) ∂(μ : Measure E)
  have hZ : 0 < Z := integral_exp_pos hi
  let g : E → ℝ := fun y => Real.exp (φ y) / Z
  have hg : Continuous g := (Real.continuous_exp.comp hφ).div_const _
  have hgp : ∀ y, 0 < g y := fun y => div_pos (Real.exp_pos _) hZ
  refine ⟨hρ.measurable.mul hg.measurable, fun x => mul_nonneg (hρ.nonneg x) (hgp x).le,
    FunctionalInequalities.KLS.LogConcave.upperSemicontinuous_mul_positive hρ.upperSemicontinuous hg hgp, ?_, ?_⟩
  · intro a b t ht0 ht1
    have hgLC : g a ^ t * g b ^ (1 - t) ≤ g (t • a + (1 - t) • b) := by
      simpa only [g, Pi.neg_apply, neg_neg] using
        FunctionalInequalities.KLS.LogConcave.rpow_mul_rpow_le_of_convexOn_readable hconc.neg hZ a b ht0 ht1
    have hρLC := hρ.logConcave a b t ht0 ht1
    change (ρ a * g a) ^ t * (ρ b * g b) ^ (1 - t) ≤ _
    rw [Real.mul_rpow (hρ.nonneg a) (hgp a).le, Real.mul_rpow (hρ.nonneg b) (hgp b).le]
    calc
      ρ a ^ t * g a ^ t * (ρ b ^ (1 - t) * g b ^ (1 - t)) =
          (ρ a ^ t * ρ b ^ (1 - t)) * (g a ^ t * g b ^ (1 - t)) := by ring
      _ ≤ _ := mul_le_mul hρLC hgLC
        (mul_nonneg (Real.rpow_nonneg (hgp a).le _) (Real.rpow_nonneg (hgp b).le _)) (hρ.nonneg _)
  · rw [hν]
    change m.withDensity (fun y => ENNReal.ofReal (ρ y * g y)) =
      (μ : Measure E).withDensity (fun y => ENNReal.ofReal (g y))
    have heq : (fun y => ENNReal.ofReal (ρ y * g y)) =
        (fun y => ENNReal.ofReal (ρ y)) * fun y => ENNReal.ofReal (g y) := by
      funext y
      exact ENNReal.ofReal_mul (hρ.nonneg y)
    rw [heq, withDensity_mul _ hρ.measurable.ennreal_ofReal hg.measurable.ennreal_ofReal,
      hρ.withDensity_eq]
