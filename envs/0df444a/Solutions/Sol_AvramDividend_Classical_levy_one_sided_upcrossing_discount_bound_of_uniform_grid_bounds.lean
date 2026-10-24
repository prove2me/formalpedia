-- Prove2me | solution 1 for AvramDividend.Classical.levy_one_sided_upcrossing_discount_bound_of_uniform_grid_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T06:54:14.977287+00:00
-- url     : https://prove2.me/submissions/1796964b-e865-4068-8104-55ad3c64305c

import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_chat03_uniform_grid_passage_clocks_measurable
import Theorems.Thm_AvramDividend_Classical_chat03_official_upper_grid_clock_tendsto
import Theorems.Thm_AvramDividend_Classical_chat03_official_no_upper_exit_grid_inf_top
import Theorems.Thm_AvramDividend_Classical_chat03_grid_upperfirst_payoff_tendsto_without_finite_ties
import Theorems.Thm_AvramDividend_Classical_chat03_grid_upperfirst_lintegral_tendsto_of_ae_payoff

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (z : ℝ)
    (mesh : ℕ → ℝ≥0)
    (hpos : ∀ n, 0 < mesh n)
    (hzero : Tendsto mesh atTop (𝓝 (0 : ℝ≥0)))
    (B : ℝ≥0∞)
    (hgrid : ∀ n : ℕ,
      (∫⁻ ω : Ω,
        let up := ⨅ k : ℕ,
          if z < X.X ((k : ℝ≥0) * mesh n) ω then
            (((k : ℝ≥0) * mesh n) : ℝ≥0∞) else ∞
        if up < (⊤ : ℝ≥0∞)
          then ENNReal.ofReal
            (Real.exp (-(q * ENNReal.toReal up)))
          else 0 ∂P) ≤ B) :
    (∫⁻ ω : Ω,
      if twoSidedExitUpTimeCorrected X z ω < (⊤ : ℝ≥0∞)
      then ENNReal.ofReal
        (Real.exp (-(q * ENNReal.toReal
          (twoSidedExitUpTimeCorrected X z ω))))
      else 0 ∂P) ≤ B := by
  letI : IsProbabilityMeasure P := X.isProbability
  let upGrid : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ⨅ k : ℕ, if z < X.X ((k : ℝ≥0) * mesh n) ω then
      (((k : ℝ≥0) * mesh n) : ℝ≥0∞) else ∞
  let downGrid : ℕ → Ω → ℝ≥0∞ := fun _ _ => ⊤
  let up : Ω → ℝ≥0∞ := fun ω => twoSidedExitUpTimeCorrected X z ω
  let down : Ω → ℝ≥0∞ := fun _ => ⊤
  have hmUp : ∀ n, Measurable (upGrid n) := by
    intro n
    exact (chat03_uniform_grid_passage_clocks_measurable
      X (0 : ℝ) z (mesh n)).1
  have hmDown : ∀ n, Measurable (downGrid n) := by
    intro n
    exact measurable_const
  have hpoint : ∀ ω : Ω, Tendsto
      (fun n => if upGrid n ω < downGrid n ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (upGrid n ω))))
        else 0) atTop
      (𝓝 (if up ω < down ω then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal (up ω))))
        else 0)) := by
    intro ω
    have hu : Tendsto (fun n => upGrid n ω) atTop (𝓝 (up ω)) :=
      chat03_official_upper_grid_clock_tendsto X ω z mesh hpos hzero
    have hd : Tendsto (fun n => downGrid n ω) atTop (𝓝 (down ω)) :=
      tendsto_const_nhds
    have hnotop : up ω = ∞ → ∀ n : ℕ, upGrid n ω = ∞ := by
      intro h n
      exact chat03_official_no_upper_exit_grid_inf_top X ω z (mesh n) h
    exact chat03_grid_upperfirst_payoff_tendsto_without_finite_ties
      q (up ω) (down ω) (fun n => upGrid n ω)
      (fun n => downGrid n ω) hu hd (by intro h; exact h) hnotop
  have hlim : Tendsto
      (fun n => ∫⁻ ω, if upGrid n ω < downGrid n ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (upGrid n ω))))
        else 0 ∂P) atTop
      (𝓝 (∫⁻ ω, if up ω < down ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (up ω))))
        else 0 ∂P)) :=
    chat03_grid_upperfirst_lintegral_tendsto_of_ae_payoff
      P q hq upGrid downGrid up down hmUp hmDown
        (Filter.Eventually.of_forall hpoint)
  have hh : (∫⁻ ω, if up ω < down ω then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal (up ω))))
        else 0 ∂P) ≤ B := by
    apply le_of_tendsto hlim
    filter_upwards [] with n
    exact hgrid n
  exact hh
