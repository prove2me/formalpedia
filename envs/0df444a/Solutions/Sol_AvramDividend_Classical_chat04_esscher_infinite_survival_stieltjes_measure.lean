-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_infinite_survival_stieltjes_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T17:22:26.081753+00:00
-- url     : https://prove2.me/submissions/292a2672-fe75-4613-b52e-1f550dbbc6dd

import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Data.ENNReal.Basic
import Theorems.Thm_AvramDividend_Classical_ennreal_monotone_right_continuous_stieltjes
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_survival_ennreal_infimum_right_continuous
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_monotone_start
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_unit_interval
import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    ∃ S : StieltjesFunction ℝ,
      ∀ x : ℝ,
        S x = (⨅ t : ℝ≥0, ENNReal.ofReal (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator (fun ω => Real.exp (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P)).toReal := by
  let F : ℝ → ℝ≥0∞ :=
    fun x => ⨅ t : ℝ≥0, ENNReal.ofReal (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator (fun ω => Real.exp (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P)
  have hmono : Monotone F := by
    intro x y hxy
    apply iInf_mono
    intro t
    exact ENNReal.ofReal_le_ofReal
      (esscher_weighted_lower_survival_mass_monotone_start X θ hθ x y hxy t)
  have hright : ∀ x : ℝ, ContinuousWithinAt F (Ici x) x := by
    intro x
    simpa only [F] using
      chat04_esscher_survival_ennreal_infimum_right_continuous X θ hθ x
  have hbound : ∀ x : ℝ, F x ≤ 1 := by
    intro x
    have hleft : F x ≤ ENNReal.ofReal (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ 0 → 0 ≤ x + X.X s ω}).indicator (fun ω => Real.exp (θ * X.X 0 ω - (0 : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P) :=
      iInf_le _ (0 : ℝ≥0)
    have hrightb : ENNReal.ofReal (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ 0 → 0 ≤ x + X.X s ω}).indicator (fun ω => Real.exp (θ * X.X 0 ω - (0 : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P) ≤ 1 := by
      simpa using ENNReal.ofReal_le_ofReal
        (esscher_weighted_lower_survival_mass_unit_interval X θ hθ x 0).2
    exact hleft.trans hrightb
  simpa only [F] using
    ennreal_monotone_right_continuous_stieltjes F hmono hright hbound
