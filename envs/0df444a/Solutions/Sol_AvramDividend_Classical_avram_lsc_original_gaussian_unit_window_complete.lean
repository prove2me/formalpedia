-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsc_original_gaussian_unit_window_complete
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T23:11:07.412199+00:00
-- url     : https://prove2.me/submissions/80ccf54b-222c-4236-8d56-c5a896646b98

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoAlgebraAssociativity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_lsc_finite_horizon_bounded_integrand_energy
import Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_abs_eval_le_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_eval_simple_readable
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical LevyStochCalc.Brownian.Ito
open scoped NNReal ENNReal
noncomputable section

/-- All deterministic window integrand obligations, and its exact original
Avram Brownian Itô representation, follow from Proved imported calculus. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱr : Filtration ℝ mΩ)
    (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱr)
    (hW : ∀ (t : ℝ) (ω : Ω),
      W.W t ω =
        (X.X (Real.toNNReal t) ω -
          (Real.toNNReal t : ℝ) * X.c) / X.σ)
    {b : ℝ} (hb : 0 < b) :
    ∃ (hm : Measurable (Function.uncurry
          (fun ω s => (stepIoc₀ Ω hb).eval s ω)))
      (hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱr
          (fun ω s => (stepIoc₀ Ω hb).eval s ω))
      (hq : ∀ T, 0 < T →
          ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖(stepIoc₀ Ω hb).eval s ω‖₊ : ℝ≥0∞) ^ 2
              ∂volume ∂P < ⊤),
      stochasticIntegralBrownian W ℱr hℱ
          (fun ω s => (stepIoc₀ Ω hb).eval s ω)
          hm hp hq b
        =ᵐ[P] fun ω =>
          (X.X (Real.toNNReal b) ω -
            (Real.toNNReal b : ℝ) * X.c) / X.σ := by
  have hm : Measurable (Function.uncurry
      (fun ω s => (stepIoc₀ Ω hb).eval s ω)) :=
    (stepIoc₀ Ω hb).eval_jointly_measurable
  have hadapt : ∀ i : Fin (stepIoc₀ Ω hb).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱr ((stepIoc₀ Ω hb).partition i.castSucc))
        ((stepIoc₀ Ω hb).ξ i) := by
    intro i
    fin_cases i
    exact MeasureTheory.stronglyMeasurable_const
  have hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱr
      (fun ω s => (stepIoc₀ Ω hb).eval s ω) :=
    (stepIoc₀ Ω hb).progressivelyMeasurable_eval ℱr
      hadapt
  have hcoeff : ∀ (i : Fin (stepIoc₀ Ω hb).N) (ω : Ω),
      |(stepIoc₀ Ω hb).ξ i ω| ≤ (1 : ℝ) := by
    intro i ω
    fin_cases i
    change |(1 : ℝ)| ≤ 1
    norm_num
  have hBound : ∀ (ω : Ω) (s : ℝ),
      |(stepIoc₀ Ω hb).eval s ω| ≤ (1 : ℝ) := by
    intro ω s
    exact SimplePredictable.abs_eval_le_readable (stepIoc₀ Ω hb)
      (by norm_num) hcoeff s ω
  have hq : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(stepIoc₀ Ω hb).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤ := by
    intro T hT
    exact avram_lsc_finite_horizon_bounded_integrand_energy
      (fun ω s => (stepIoc₀ Ω hb).eval s ω)
      1 (by norm_num) hBound T hT
  have hWindow (ω : Ω) :
      (stepIoc₀ Ω hb).integralAgainst W.W b ω =
        W.W b ω - W.W 0 ω := by
    have hrw : (stepIoc₀ Ω hb).integralAgainst W.W b ω =
        ∑ i : Fin 1,
          (![fun _ => (1 : ℝ)] : Fin 1 → Ω → ℝ) i ω *
            (W.W (min ((![0, b] : Fin 2 → ℝ) i.succ) b) ω -
              W.W (min ((![0, b] : Fin 2 → ℝ) i.castSucc) b) ω) := rfl
    rw [hrw, Fin.sum_univ_one]
    simp [min_eq_left hb.le]
  have hIto :=
    stochasticIntegralBrownian_eval_simple_readable W ℱr hℱ
      (stepIoc₀ Ω hb) hadapt hm hp hq hb.le
  have hResult :
      stochasticIntegralBrownian W ℱr hℱ
        (fun ω s => (stepIoc₀ Ω hb).eval s ω) hm hp hq b
      =ᵐ[P] fun ω =>
        (X.X (Real.toNNReal b) ω -
          (Real.toNNReal b : ℝ) * X.c) / X.σ := by
    filter_upwards [hIto, W.initial_zero] with ω hInt hZero
    calc
      stochasticIntegralBrownian W ℱr hℱ
          (fun ω s => (stepIoc₀ Ω hb).eval s ω) hm hp hq b ω
          = (stepIoc₀ Ω hb).integralAgainst W.W b ω := hInt
      _ = W.W b ω - W.W 0 ω := by
        exact hWindow ω
      _ = (X.X (Real.toNNReal b) ω -
          (Real.toNNReal b : ℝ) * X.c) / X.σ := by
        simpa [hZero] using hW b ω
  exact ⟨hm, hp, hq, hResult⟩
