-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f16_sigma_zero_infinite_jump_upward_germ_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T01:20:49.854296+00:00
-- url     : https://prove2.me/submissions/ae276f88-a855-4c05-93a5-c943bb0ab241

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_DurrettProbability_Brownian
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_root_of_notBV
import Theorems.Thm_AvramDividend_Classical_avram_p4_f18_positive_roots_uniform_early_upcrossing_mass
import Theorems.Thm_AvramDividend_Classical_avram_p4_f15_continuousWithin_positive_rational_witness
import Theorems.Thm_AvramDividend_Classical_avram_p4_f17_uniform_rational_early_mass_to_germ_mass
import Theorems.Thm_AvramDividend_Classical_avram_p4_f14_original_near_zero_rational_path_equiv
import Theorems.Thm_AvramDividend_Classical_avram_p4_f12_original_positive_near_zero_germ_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_f12_original_positive_germ_mass_to_ae

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical DurrettProbability
open scoped NNReal ENNReal
noncomputable section

/-- Unbounded variation forces almost-sure positive excursions near zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hσ : X.σ = 0)
    (hν : ¬ ∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν < ⊤) :
    0 < P.real {ω : Ω | ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ 0 < X.X s ω} := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hvar : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤ := by
    by_contra hne
    exact hν (lt_top_iff_ne_top.mpr hne)
  have hnbv : ¬ X.BoundedVariation :=
    avram_wave3_01_infinite_small_jump_not_bv X hvar
  have hroots : ∀ q : ℝ, 0 < q → ∃ φ : ℝ, 0 < φ ∧ X.ψ φ = q := by
    intro q hq
    exact unbounded_esscher_root_of_notBV X q hq hnbv
  let A : Set Ω := {ω | ∀ ε : ℝ≥0, 0 < ε →
    ∃ s : ℝ≥0, s < ε ∧ 0 < X.X s ω}
  have hAm : MeasurableSet[germSigma X.X] A :=
    avram_p4_f12_original_positive_near_zero_germ_measurable X
  have hB (r : ℚ≥0) : Measurable (X.X (r : ℝ≥0)) :=
    (X.adapted (r : ℝ≥0)).mono (𝓕.le _) le_rfl
  have hUniform : ∀ ε : ℝ≥0, 0 < ε →
      (1 / 10 : ℝ≥0∞) ≤
        P {ω : Ω | ∃ r : ℚ≥0, (r : ℝ≥0) < ε ∧ 0 < X.X (r : ℝ≥0) ω} := by
    intro ε hε
    let R : Set Ω := {ω | ∃ s : ℝ≥0, s < ε ∧ 0 < X.X s ω}
    let S : Set Ω := {ω | ∃ r : ℚ≥0, (r : ℝ≥0) < ε ∧ 0 < X.X (r : ℝ≥0) ω}
    have hRmass : (1 / 10 : ℝ) ≤ P.real R :=
      avram_p4_f18_positive_roots_uniform_early_upcrossing_mass X hroots ε hε
    have hRS : R ⊆ S := by
      rintro ω ⟨s, hsε, hsPos⟩
      obtain ⟨r, _hsr, hrε, hrPos⟩ :=
        avram_p4_f15_continuousWithin_positive_rational_witness
          (fun t => X.X t ω) s ε hsε hsPos (X.rightCont ω s)
      exact ⟨r, hrε, hrPos⟩
    have hSmass : (1 / 10 : ℝ) ≤ P.real S :=
      hRmass.trans (measureReal_mono hRS)
    have hSfinite : P S ≠ ⊤ := (measure_lt_top P S).ne
    have hSmall : ENNReal.ofReal (P.real S) = P S :=
      ENNReal.ofReal_toReal hSfinite
    change (1 / 10 : ℝ≥0∞) ≤ P S
    rw [← hSmall]
    have hPos : (1 / 10 : ℝ≥0∞) = ENNReal.ofReal (1 / 10 : ℝ) := by
      norm_num [ENNReal.ofReal_div_of_pos]
    rw [hPos]
    exact ENNReal.ofReal_le_ofReal hSmass
  have hGermPos : 0 < P.real {ω : Ω | ∀ ε : ℝ≥0, 0 < ε →
      ∃ r : ℚ≥0, (r : ℝ≥0) < ε ∧ 0 < X.X (r : ℝ≥0) ω} :=
    avram_p4_f17_uniform_rational_early_mass_to_germ_mass
      P (fun t ω => X.X t ω) hB (1 / 10) (by norm_num) hUniform
  have hEq := avram_p4_f14_original_near_zero_rational_path_equiv X
  have hPosA : 0 < P.real A := by
    rw [← hEq] at hGermPos
    exact hGermPos
  exact hPosA
