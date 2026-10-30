-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_01_finite_killed_markov_real
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T08:51:46.352269+00:00
-- url     : https://prove2.me/submissions/fad9fa93-b4e7-4845-a0dc-ff170b360b3f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_finite_killed_markov_ennreal
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_history_survival_weight_integrable
import Theorems.Thm_AvramDividend_Classical_esscher_exp_process_integrable
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_unit_interval
import Theorems.Thm_AvramDividend_Classical_chat04_shifted_lower_survival_measurable_no_schedule

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-- Actual source-Lévy finite killed Markov identity in real Bochner integrals,
using independently Proved finite ENNReal Markov and integrability theorems. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (x : ℝ) (s u : ℝ≥0)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (hTerminal : ∃ j : ℕ, τ j = u) :
    (∫ ω, ({ω | ∀ v : ℝ≥0, v ≤ s + u → 0 ≤ x + X.X v ω}).indicator
      (fun ω => Real.exp
        (θ * X.X (s + u) ω - ((s + u : ℝ≥0) : ℝ) *
          laplaceExponent X.c X.σ X.ν θ)) ω ∂P) =
    (∫ ω : Ω,
      ({ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω}).indicator
        (fun ω => Real.exp
          (θ * X.X s ω - (s : ℝ) * laplaceExponent X.c X.σ X.ν θ) *
          (∫ ζ,
            ({ζ | ∀ v : ℝ≥0, v ≤ u → 0 ≤ (x + X.X s ω) + X.X v ζ}).indicator
              (fun ζ => Real.exp
                (θ * X.X u ζ - (u : ℝ) *
                  laplaceExponent X.c X.σ X.ν θ)) ζ ∂P)) ω ∂P) := by
  classical
  let Bt : Set Ω := {ω | ∀ v : ℝ≥0, v ≤ s + u → 0 ≤ x + X.X v ω}
  let Bs : Set Ω := {ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω}
  let Mt : Ω → ℝ := fun ω =>
    Real.exp (θ * X.X (s + u) ω - ((s + u : ℝ≥0) : ℝ) *
      laplaceExponent X.c X.σ X.ν θ)
  let Ms : Ω → ℝ := fun ω =>
    Real.exp (θ * X.X s ω - (s : ℝ) * laplaceExponent X.c X.σ X.ν θ)
  let F : ℝ → ℝ := fun z =>
    ∫ ζ, ({ζ | ∀ v : ℝ≥0, v ≤ u → 0 ≤ z + X.X v ζ}).indicator
      (fun ζ => Real.exp
        (θ * X.X u ζ - (u : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ζ ∂P
  have hBt : MeasurableSet Bt :=
    chat04_shifted_lower_survival_measurable_no_schedule X x (s + u)
  have hLI : Integrable (Bt.indicator Mt) P :=
    (esscher_exp_process_integrable X θ hθ (s + u)).indicator hBt
  have hRI : Integrable (Bs.indicator
      (fun ω => Ms ω * F (x + X.X s ω))) P :=
    avram_root29_01_history_survival_weight_integrable X θ hθ x s u
  have hL0 : ∀ ω, 0 ≤ Bt.indicator Mt ω := by
    intro ω
    by_cases hw : ω ∈ Bt
    · rw [Set.indicator_of_mem hw]
      exact (Real.exp_pos _).le
    · rw [Set.indicator_of_notMem hw]
  have hR0 : ∀ ω, 0 ≤ Bs.indicator
      (fun ω => Ms ω * F (x + X.X s ω)) ω := by
    intro ω
    by_cases hw : ω ∈ Bs
    · rw [Set.indicator_of_mem hw]
      exact mul_nonneg (Real.exp_pos _).le
        (esscher_weighted_lower_survival_mass_unit_interval
          X θ hθ (x + X.X s ω) u).1
    · rw [Set.indicator_of_notMem hw]
  have hEq : ENNReal.ofReal (∫ ω, Bt.indicator Mt ω ∂P) =
      ENNReal.ofReal (∫ ω, Bs.indicator
        (fun ω => Ms ω * F (x + X.X s ω)) ω ∂P) := by
    rw [ofReal_integral_eq_lintegral_ofReal hLI (ae_of_all _ hL0),
      ofReal_integral_eq_lintegral_ofReal hRI (ae_of_all _ hR0)]
    calc
      (∫⁻ ω, ENNReal.ofReal (Bt.indicator Mt ω) ∂P) =
          (∫⁻ ω, Bt.indicator (fun ω => ENNReal.ofReal (Mt ω)) ω ∂P) := by
        apply lintegral_congr
        intro ω
        by_cases hw : ω ∈ Bt
        · simp [Set.indicator_of_mem hw]
        · simp [Set.indicator_of_notMem hw]
      _ = (∫⁻ ω : Ω,
          (if ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω then
            ENNReal.ofReal (Ms ω) * ENNReal.ofReal (F (x + X.X s ω))
           else (0 : ℝ≥0∞)) ∂P) := by
        simpa only [Bt, Mt, Ms, F] using
          (avram_root29_01_finite_killed_markov_ennreal
            X θ hθ x s u τ hCover hTerminal)
      _ = (∫⁻ ω, ENNReal.ofReal
          (Bs.indicator (fun ω => Ms ω * F (x + X.X s ω)) ω) ∂P) := by
        apply lintegral_congr
        intro ω
        by_cases hw : ω ∈ Bs
        · have hp : ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω := hw
          simp only [Set.indicator_of_mem hw, if_pos hp]
          rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
        · have hp : ¬ (∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω) := hw
          simp [Set.indicator_of_notMem hw, hp]
  have hLp : 0 ≤ ∫ ω, Bt.indicator Mt ω ∂P := integral_nonneg hL0
  have hRp : 0 ≤ ∫ ω, Bs.indicator
      (fun ω => Ms ω * F (x + X.X s ω)) ω ∂P := integral_nonneg hR0
  change (∫ ω, Bt.indicator Mt ω ∂P) =
    (∫ ω, Bs.indicator (fun ω => Ms ω * F (x + X.X s ω)) ω ∂P)
  have hRe := congrArg ENNReal.toReal hEq
  simpa only [ENNReal.toReal_ofReal hLp, ENNReal.toReal_ofReal hRp] using hRe
