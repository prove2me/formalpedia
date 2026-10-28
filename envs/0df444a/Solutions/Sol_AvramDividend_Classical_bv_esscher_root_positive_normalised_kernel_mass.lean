-- Prove2me | solution 1 for AvramDividend.Classical.bv_esscher_root_positive_normalised_kernel_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T12:33:57.563989+00:00
-- url     : https://prove2.me/submissions/56b81d10-38da-441a-985c-e898ac0b7d98

import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_negative_measure_magnitude_pushforward_positive
import Theorems.Thm_AvramDividend_Classical_esscher_exponential_withDensity_nonzero_of_nonzero
import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_real_integral_pos_of_nonzero_no_zero_atom
import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_density_total_mass
import Theorems.Thm_AvramDividend_Classical_esscher_tail_kernel_mass_as_discounted_first_moment
import Theorems.Thm_AvramDividend_Classical_bv_esscher_root_subcritical_kernel_mass
import Theorems.Thm_AvramDividend_Classical_bv_esscher_positive_tail_real_mass_over_drift_subunit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A BV standing Lévy process has a genuinely positive, subunit Esscher renewal mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    0 <
      (∫ t in Ioi (0 : ℝ),
        ENNReal.toReal (((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
          (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
          {z : ℝ≥0 | t < (z : ℝ)}) ∂volume) / X.drift ∧
    (∫ t in Ioi (0 : ℝ),
        ENNReal.toReal (((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
          (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
          {z : ℝ≥0 | t < (z : ℝ)}) ∂volume) / X.drift < 1 := by
  let μ : Measure ℝ≥0 := X.ν.map (fun y : ℝ => Real.toNNReal (-y))
  let μφ : Measure ℝ≥0 := μ.withDensity
    (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))))
  have hf : Measurable (fun y : ℝ => Real.toNNReal (-y)) := by
    fun_prop
  have hpre : (fun y : ℝ => Real.toNNReal (-y)) ⁻¹'
      ({0} : Set ℝ≥0) = Ici (0 : ℝ) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_Ici,
      Real.toNNReal_eq_zero]
    constructor
    · intro h
      linarith
    · intro h
      linarith
  have hμzero : μ ({0} : Set ℝ≥0) = 0 := by
    change (X.ν.map (fun y : ℝ => Real.toNNReal (-y))) {0} = 0
    rw [Measure.map_apply hf (measurableSet_singleton (0 : ℝ≥0)), hpre]
    exact X.ν_Ici
  have hμpos : 0 < μ (Ioi (0 : ℝ≥0)) :=
    negative_measure_magnitude_pushforward_positive X.ν X.ν_Ici
      (bv_standing_drift_pos X hX hbv).2 hf
  have hμne : μ ≠ 0 := by
    intro h
    simp [h] at hμpos
  have hweight : AEMeasurable
      (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))) μ := by
    fun_prop
  have hμφne : μφ ≠ 0 :=
    esscher_exponential_withDensity_nonzero_of_nonzero μ hμne φ hweight
  have hμφzero : μφ ({0} : Set ℝ≥0) = 0 :=
    withDensity_absolutelyContinuous _ _ hμzero
  have hfirst : (∫⁻ z : ℝ≥0, ENNReal.ofReal (z : ℝ) ∂μφ) < ⊤ := by
    rw [← positive_jump_tail_density_total_mass,
      esscher_tail_kernel_mass_as_discounted_first_moment μ φ]
    exact (bv_esscher_root_subcritical_kernel_mass
      X hbv q hq φ hφ hroot).1.lintegral_lt_top
  have hpositive : 0 < ∫ t in Ioi (0 : ℝ),
      ENNReal.toReal (μφ {z : ℝ≥0 | t < (z : ℝ)}) ∂volume :=
    positive_jump_tail_real_integral_pos_of_nonzero_no_zero_atom
      μφ hμφzero hμφne hfirst
  have hdrift : 0 < X.drift := (bv_standing_drift_pos X hX hbv).1
  exact ⟨div_pos hpositive hdrift,
    (bv_esscher_positive_tail_real_mass_over_drift_subunit
      X hbv q hq φ hφ hroot).2⟩
