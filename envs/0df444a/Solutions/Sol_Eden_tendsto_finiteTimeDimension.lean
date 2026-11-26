-- Prove2me | solution 1 for Eden.tendsto_finiteTimeDimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:23:37.20508+00:00
-- url     : https://prove2.me/submissions/0206fb2f-cd0b-412a-b967-c89c0c0d9bc2

import Definitions.Def_Eden_DimensionConvergenceCriteria
import Definitions.Def_Eden_NeutralDimensionBounds
import Definitions.Def_Eden_LimitingInterpolation
import Definitions.Def_Eden_DimensionConvergence
import Theorems.Thm_Eden_tendsto_finiteTimeDimension_of_asymptotic_zero
import Theorems.Thm_Eden_tendsto_finiteTimeDimension_of_spectrum_pos
import Theorems.Thm_Eden_descending_radiusPairSpectrum_one_one
import Theorems.Thm_Eden_descending_radiusPairSpectrum_one_two
import Theorems.Thm_Eden_descending_radiusPairSpectrum_swap
import Theorems.Thm_Eden_descending_radiusPairSpectrum_two_two
import Theorems.Thm_Eden_descending_radiusPairSpectrum_zero_one
import Theorems.Thm_Eden_descending_radiusPairSpectrum_zero_two
import Theorems.Thm_Eden_descending_radiusPairSpectrum_zero_zero
import Theorems.Thm_Eden_finiteTimeDimension_ge_one_of_first_radius
import Theorems.Thm_Eden_finiteTimeDimension_ge_one_of_second_radius
import Theorems.Thm_Eden_finiteTimeDimension_ge_two_of_radii
import Theorems.Thm_Eden_kaplanYorkeDimension_one_one
import Theorems.Thm_Eden_kaplanYorkeDimension_one_two
import Theorems.Thm_Eden_kaplanYorkeDimension_two_two
import Theorems.Thm_Eden_kaplanYorkeDimension_zero_one
import Theorems.Thm_Eden_kaplanYorkeDimension_zero_two
import Theorems.Thm_Eden_kaplanYorkeDimension_zero_zero
import Theorems.Thm_Eden_limitingSquaredRadius_cases
import Theorems.Thm_Eden_lyapunovExponent_eq_radiusPairSpectrum
import Theorems.Thm_Eden_one_lt_of_limitingSquaredRadius_eq_two
import Theorems.Thm_Eden_spectrumInterpolation_pos_one_one
import Theorems.Thm_Eden_spectrumInterpolation_pos_one_two
import Theorems.Thm_Eden_spectrumInterpolation_pos_zero_one
import Theorems.Thm_Eden_tendsto_finiteTimeDimension_of_eventual_lower_bound

section
noncomputable section
open Set Filter
open scoped Topology
namespace Eden
private theorem convergence_zero_one {c : ℝ} (hc : 4 < c) (p : PhaseSpace)
    (ha : lyapunovExponent c p = ![2, 0, -2, -2, -c]) :
    Tendsto (fun t => finiteTimeDimension c t p) atTop (𝓝 (asymptoticDimension c p)) := by
  apply tendsto_finiteTimeDimension_of_spectrum_pos c p _ ha
  intro d hd
  rw [kaplanYorkeDimension_zero_one hc] at hd
  exact spectrumInterpolation_pos_zero_one hd
private theorem convergence_one_one {c : ℝ} (hc : 4 < c) (p : PhaseSpace)
    (ha : lyapunovExponent c p = ![2, 2, 0, 0, -c]) :
    Tendsto (fun t => finiteTimeDimension c t p) atTop (𝓝 (asymptoticDimension c p)) := by
  apply tendsto_finiteTimeDimension_of_spectrum_pos c p _ ha
  intro d hd
  rw [kaplanYorkeDimension_one_one hc] at hd
  exact spectrumInterpolation_pos_one_one hc hd
private theorem convergence_one_two {c : ℝ} (hc : 4 < c) (p : PhaseSpace)
    (ha : lyapunovExponent c p = ![2, 0, 0, -4, -c]) :
    Tendsto (fun t => finiteTimeDimension c t p) atTop (𝓝 (asymptoticDimension c p)) := by
  apply tendsto_finiteTimeDimension_of_spectrum_pos c p _ ha
  intro d hd
  rw [kaplanYorkeDimension_one_two hc] at hd
  exact spectrumInterpolation_pos_one_two hd
end Eden
end
end

set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ attractor) :
    Tendsto (fun t => finiteTimeDimension c t p) atTop (𝓝 (asymptoticDimension c p)) := by
  have ha := lyapunovExponent_eq_radiusPairSpectrum c p
  rcases limitingSquaredRadius_cases (radiusSq₁ p) with h₁ | h₁ | h₁ <;>
    rcases limitingSquaredRadius_cases (radiusSq₂ p) with h₂ | h₂ | h₂
  all_goals rw [h₁, h₂] at ha
  · apply tendsto_finiteTimeDimension_of_asymptotic_zero c p
    rw [asymptoticDimension, ha, descending_radiusPairSpectrum_zero_zero hc,
      kaplanYorkeDimension_zero_zero hc]
  · exact convergence_zero_one hc p
      (ha.trans (descending_radiusPairSpectrum_zero_one hc))
  · have hdim : asymptoticDimension c p = 1 := by
      rw [asymptoticDimension, ha, descending_radiusPairSpectrum_zero_two hc,
        kaplanYorkeDimension_zero_two hc]
    apply tendsto_finiteTimeDimension_of_eventual_lower_bound c p
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [hdim]
    exact finiteTimeDimension_ge_one_of_second_radius c ht hp
      (one_lt_of_limitingSquaredRadius_eq_two h₂).le
  · rw [descending_radiusPairSpectrum_swap c 1 0] at ha
    exact convergence_zero_one hc p
      (ha.trans (descending_radiusPairSpectrum_zero_one hc))
  · exact convergence_one_one hc p
      (ha.trans (descending_radiusPairSpectrum_one_one hc))
  · exact convergence_one_two hc p
      (ha.trans (descending_radiusPairSpectrum_one_two hc))
  · rw [descending_radiusPairSpectrum_swap c 2 0] at ha
    have hdim : asymptoticDimension c p = 1 := by
      rw [asymptoticDimension, ha, descending_radiusPairSpectrum_zero_two hc,
        kaplanYorkeDimension_zero_two hc]
    apply tendsto_finiteTimeDimension_of_eventual_lower_bound c p
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [hdim]
    exact finiteTimeDimension_ge_one_of_first_radius c ht hp
      (one_lt_of_limitingSquaredRadius_eq_two h₁).le
  · rw [descending_radiusPairSpectrum_swap c 2 1] at ha
    exact convergence_one_two hc p
      (ha.trans (descending_radiusPairSpectrum_one_two hc))
  · have hdim : asymptoticDimension c p = 2 := by
      rw [asymptoticDimension, ha, descending_radiusPairSpectrum_two_two hc,
        kaplanYorkeDimension_two_two hc]
    apply tendsto_finiteTimeDimension_of_eventual_lower_bound c p
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [hdim]
    exact finiteTimeDimension_ge_two_of_radii c ht hp
      (one_lt_of_limitingSquaredRadius_eq_two h₁).le
      (one_lt_of_limitingSquaredRadius_eq_two h₂).le
end Eden
