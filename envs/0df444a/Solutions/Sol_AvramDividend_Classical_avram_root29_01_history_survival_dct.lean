-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_01_history_survival_dct
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T09:06:40.629598+00:00
-- url     : https://prove2.me/submissions/6fa445d8-1fbf-479c-8d0d-1b6f2eb6a6ed

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Theorems.Thm_AvramDividend_Classical_esscher_exp_process_integrable
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_unit_interval
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_monotone_start
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_tendsto_iInf
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_antitone
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_history_survival_weight_integrable
import Theorems.Thm_AvramDividend_Classical_chat04_shifted_lower_survival_measurable_no_schedule

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal

/-- Original-P dominated convergence of the true historical survival reward
towards the perpetual finite-Esscher survival mass at the random reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (x : ℝ) (s : ℝ≥0) :
    Tendsto
      (fun u : ℝ≥0 => ∫ ω,
        ({ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω}).indicator
          (fun ω => Real.exp
            (θ * X.X s ω - (s : ℝ) * laplaceExponent X.c X.σ X.ν θ) *
              (∫ ζ,
                ({ζ | ∀ v : ℝ≥0, v ≤ u → 0 ≤ (x + X.X s ω) + X.X v ζ}).indicator
                  (fun ζ => Real.exp
                    (θ * X.X u ζ - (u : ℝ) *
                      laplaceExponent X.c X.σ X.ν θ)) ζ ∂P)) ω ∂P)
      atTop
      (nhds (∫ ω,
        ({ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω}).indicator
          (fun ω => Real.exp
            (θ * X.X s ω - (s : ℝ) * laplaceExponent X.c X.σ X.ν θ) *
              (⨅ u : ℝ≥0, ∫ ζ,
                ({ζ | ∀ v : ℝ≥0, v ≤ u → 0 ≤ (x + X.X s ω) + X.X v ζ}).indicator
                  (fun ζ => Real.exp
                    (θ * X.X u ζ - (u : ℝ) *
                      laplaceExponent X.c X.σ X.ν θ)) ζ ∂P)) ω ∂P)) := by
  let B : Set Ω :=
    {ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω}
  let M : Ω → ℝ := fun ω =>
    Real.exp (θ * X.X s ω - (s : ℝ) * laplaceExponent X.c X.σ X.ν θ)
  let F : ℝ≥0 → ℝ → ℝ := fun u z =>
    ∫ ζ, ({ζ | ∀ v : ℝ≥0, v ≤ u → 0 ≤ z + X.X v ζ}).indicator
      (fun ζ => Real.exp
        (θ * X.X u ζ - (u : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ζ ∂P
  have hB : MeasurableSet B :=
    chat04_shifted_lower_survival_measurable_no_schedule X x s
  have hXs : Measurable (X.X s) := (X.adapted s).mono (𝓕.le s) le_rfl
  have hMm : Measurable M :=
    Real.continuous_exp.measurable.comp
      ((measurable_const.mul hXs).sub measurable_const)
  have hIntM : Integrable M P := esscher_exp_process_integrable X θ hθ s
  let R : ℝ≥0 → ℝ := fun u =>
    ∫ ω, B.indicator (fun ω => M ω * F u (x + X.X s ω)) ω ∂P
  let L : ℝ := ∫ ω, B.indicator
    (fun ω => M ω * (⨅ u, F u (x + X.X s ω))) ω ∂P
  change Tendsto R atTop (nhds L)
  have hNat : Tendsto (fun n : ℕ => R (n : ℝ≥0)) atTop (nhds L) := by
    change Tendsto (fun n : ℕ => ∫ ω, B.indicator
        (fun ω => M ω * F (n : ℝ≥0) (x + X.X s ω)) ω ∂P)
      atTop (nhds L)
    apply tendsto_integral_of_dominated_convergence M
    · intro n
      have hFmono : Monotone (F (n : ℝ≥0)) := by
        intro a b hab
        exact esscher_weighted_lower_survival_mass_monotone_start
          X θ hθ a b hab (n : ℝ≥0)
      have hFu : Measurable (F (n : ℝ≥0)) := hFmono.measurable
      exact ((hMm.mul (hFu.comp (measurable_const.add hXs))).indicator
        hB).aestronglyMeasurable
    · exact hIntM
    · intro n
      filter_upwards with ω
      by_cases hw : ω ∈ B
      · rw [Set.indicator_of_mem hw]
        have hunit := esscher_weighted_lower_survival_mass_unit_interval
          X θ hθ (x + X.X s ω) (n : ℝ≥0)
        calc
          ‖M ω * F (n : ℝ≥0) (x + X.X s ω)‖ =
              M ω * F (n : ℝ≥0) (x + X.X s ω) := by
            rw [Real.norm_eq_abs,
              abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hunit.1)]
          _ ≤ M ω * 1 :=
            mul_le_mul_of_nonneg_left hunit.2 (Real.exp_pos _).le
          _ = M ω := mul_one _
      · rw [Set.indicator_of_notMem hw, norm_zero]
        exact (Real.exp_pos _).le
    · filter_upwards with ω
      by_cases hw : ω ∈ B
      · have hF := (esscher_weighted_lower_survival_mass_tendsto_iInf
          X θ hθ (x + X.X s ω)).comp
            (tendsto_natCast_atTop_atTop :
              Tendsto (fun n : ℕ => (n : ℝ≥0)) atTop atTop)
        have hFt :
            Tendsto (fun n : ℕ => F (n : ℝ≥0) (x + X.X s ω))
              atTop (nhds (⨅ u : ℝ≥0, F u (x + X.X s ω))) := by
          exact hF
        simpa only [Set.indicator_of_mem hw] using
          (tendsto_const_nhds.mul hFt)
      · simpa only [Set.indicator_of_notMem hw] using
          (tendsto_const_nhds :
            Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  have hAnti : Antitone R := by
    intro t u htu
    have hPoint (ω : Ω) :
        B.indicator (fun ω => M ω * F u (x + X.X s ω)) ω ≤
          B.indicator (fun ω => M ω * F t (x + X.X s ω)) ω := by
      by_cases hw : ω ∈ B
      · simp only [Set.indicator_of_mem hw]
        exact mul_le_mul_of_nonneg_left
          (esscher_weighted_lower_survival_mass_antitone
            X θ hθ (x + X.X s ω) t u htu) (Real.exp_pos _).le
      · simp only [Set.indicator_of_notMem hw, le_refl]
    exact integral_mono
      (avram_root29_01_history_survival_weight_integrable X θ hθ x s u)
      (avram_root29_01_history_survival_weight_integrable X θ hθ x s t)
      hPoint
  have hBelow : BddBelow (Set.range R) := by
    refine ⟨0, ?_⟩
    rintro y ⟨u, rfl⟩
    apply integral_nonneg
    intro ω
    by_cases hw : ω ∈ B
    · rw [Set.indicator_of_mem hw]
      exact mul_nonneg (Real.exp_pos _).le
        (esscher_weighted_lower_survival_mass_unit_interval
          X θ hθ (x + X.X s ω) u).1
    · rw [Set.indicator_of_notMem hw]
      exact le_refl _
  have hAll : Tendsto R atTop (nhds (⨅ u, R u)) :=
    tendsto_atTop_ciInf hAnti hBelow
  have hSub : Tendsto (fun n : ℕ => R (n : ℝ≥0))
      atTop (nhds (⨅ u, R u)) :=
    hAll.comp (tendsto_natCast_atTop_atTop :
      Tendsto (fun n : ℕ => (n : ℝ≥0)) atTop atTop)
  have hEq : (⨅ u, R u) = L := tendsto_nhds_unique hSub hNat
  rw [hEq] at hAll
  exact hAll
