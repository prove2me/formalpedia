-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f16_sigma_nonzero_upward_germ_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T13:45:17.547309+00:00
-- url     : https://prove2.me/submissions/55bf710c-6507-4db1-a3b5-3ec076b8737d

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_gaussian
import Theorems.Thm_AvramDividend_Classical_avram_p4_f18_positive_roots_uniform_early_upcrossing_mass
import Theorems.Thm_AvramDividend_Classical_avram_p4_f15_continuousWithin_positive_rational_witness
import Theorems.Thm_AvramDividend_Classical_avram_p4_f17_uniform_rational_early_mass_to_germ_mass
import Theorems.Thm_AvramDividend_Classical_avram_p4_f14_original_near_zero_rational_path_equiv

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! The sole genuinely open imported result is the existing early-upcrossing
    mass estimate. All other arguments transport it to the actual path germ. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hσ : X.σ ≠ 0) :
    0 < P.real {ω : Ω | ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ 0 < X.X s ω} := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hσpos : 0 < X.σ := lt_of_le_of_ne X.σ_nonneg (Ne.symm hσ)
  have hroots : ∀ q : ℝ, 0 < q → ∃ φ : ℝ, 0 < φ ∧ X.ψ φ = q := by
    intro q hq
    exact positive_esscher_root_of_gaussian X q hq hσpos
  let a : ℝ≥0∞ := ENNReal.ofReal (1 / 10 : ℝ)
  have ha : 0 < a := by dsimp [a]; norm_num
  have hB (q : ℚ≥0) : Measurable (X.X (q : ℝ≥0)) :=
    (X.adapted (q : ℝ≥0)).mono (𝓕.le _) le_rfl
  have hUniform : ∀ ε : ℝ≥0, 0 < ε →
      a ≤ P {ω : Ω | ∃ q : ℚ≥0,
        (q : ℝ≥0) < ε ∧ 0 < X.X (q : ℝ≥0) ω} := by
    intro ε hε
    let E : Set Ω := {ω | ∃ s : ℝ≥0, s < ε ∧ 0 < X.X s ω}
    let F : Set Ω := {ω | ∃ q : ℚ≥0,
      (q : ℝ≥0) < ε ∧ 0 < X.X (q : ℝ≥0) ω}
    have hEF : E ⊆ F := by
      intro ω hω
      obtain ⟨s, hsε, hspos⟩ := hω
      obtain ⟨q, _hsq, hqε, hqpos⟩ :=
        avram_p4_f15_continuousWithin_positive_rational_witness
          (fun t => X.X t ω) s ε hsε hspos (X.rightCont ω s)
      exact ⟨q, hqε, hqpos⟩
    have hReal : (1 / 10 : ℝ) ≤ P.real E := by
      simpa only [E] using
        (avram_p4_f18_positive_roots_uniform_early_upcrossing_mass
          X hroots ε hε)
    have hfinite : P E ≠ ⊤ := (measure_lt_top P E).ne
    have hBound : a ≤ P E := by
      calc
        a = ENNReal.ofReal (1 / 10 : ℝ) := rfl
        _ ≤ ENNReal.ofReal (P.real E) := ENNReal.ofReal_le_ofReal hReal
        _ = P E := by simp [Measure.real, ENNReal.ofReal_toReal hfinite]
    exact hBound.trans (measure_mono hEF)
  have hGerm :=
    avram_p4_f17_uniform_rational_early_mass_to_germ_mass
      P (fun t ω => X.X t ω) hB a ha hUniform
  rw [avram_p4_f14_original_near_zero_rational_path_equiv X]
  exact hGerm
