-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f18_positive_roots_uniform_early_upcrossing_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T14:26:57.929369+00:00
-- url     : https://prove2.me/submissions/2fdea39f-2184-47bb-8825-846cbe0710b0

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_levy_positive_root_exact_strict_upcrossing_discount
import Theorems.Thm_AvramDividend_Classical_avram_p4_f18_discounted_finite_clock_split_le
import Theorems.Thm_AvramDividend_Classical_avram_p4_f19_strict_upclock_before_horizon_has_path_witness
import Theorems.Thm_AvramDividend_Classical_avram_p4_f15_continuousWithin_positive_rational_witness

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! Use exact first-passage discount, strict upper-clock witness and the
    countable positive path event to deduce a uniform pre-horizon mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hroots : ∀ q : ℝ, 0 < q → ∃ φ : ℝ, 0 < φ ∧ X.ψ φ = q) :
    ∀ ε : ℝ≥0, 0 < ε →
      (1 / 10 : ℝ) ≤ P.real {ω : Ω | ∃ s : ℝ≥0, s < ε ∧ 0 < X.X s ω} := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro ε hε
  have hεreal : 0 < (ε : ℝ) := by exact_mod_cast hε
  let q : ℝ := Real.log 4 / (ε : ℝ)
  have hq : 0 < q := div_pos (Real.log_pos (by norm_num)) hεreal
  obtain ⟨φ, hφ, hroot⟩ := hroots q hq
  let z : ℝ := Real.log 2 / φ
  have hz : 0 < z := div_pos (Real.log_pos (by norm_num)) hφ
  have hqe : q * (ε : ℝ) = Real.log 4 := by
    dsimp [q]
    field_simp
  have hφz : φ * z = Real.log 2 := by
    dsimp [z]
    field_simp
  have hb : ENNReal.ofReal (Real.exp (-(q * (ε : ℝ)))) = 1 / 4 := by
    rw [hqe, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    norm_num [ENNReal.ofReal_div_of_pos]
  have hc : ENNReal.ofReal (Real.exp (-(φ * z))) = 1 / 2 := by
    rw [hφz, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num [ENNReal.ofReal_div_of_pos]
  let A : Set Ω := {ω | ∃ r : ℚ≥0,
    (r : ℝ≥0) < ε ∧ 0 < X.X (r : ℝ≥0) ω}
  have hB (r : ℚ≥0) : Measurable (X.X (r : ℝ≥0)) :=
    (X.adapted (r : ℝ≥0)).mono (𝓕.le _) le_rfl
  have hA : MeasurableSet A := by
    have hAr : MeasurableSet (⋃ r : ℚ≥0,
        {ω : Ω | (r : ℝ≥0) < ε ∧ 0 < X.X (r : ℝ≥0) ω}) := by
      refine MeasurableSet.iUnion fun r => ?_
      by_cases hr : (r : ℝ≥0) < ε
      · simpa [hr] using measurableSet_lt measurable_const (hB r)
      · simp [hr]
    have hEq : A = ⋃ r : ℚ≥0,
        {ω : Ω | (r : ℝ≥0) < ε ∧ 0 < X.X (r : ℝ≥0) ω} := by
      ext ω
      simp only [A, Set.mem_iUnion, Set.mem_setOf_eq]
    rw [hEq]
    exact hAr
  let τ : Ω → ℝ≥0∞ := twoSidedExitUpTimeCorrected X z
  let F : Ω → ℝ≥0∞ := fun ω =>
    if τ ω < ⊤ then ENNReal.ofReal
      (Real.exp (-(q * ENNReal.toReal (τ ω)))) else 0
  have hτA (ω : Ω) (ht : τ ω < (ε : ℝ≥0∞)) : ω ∈ A := by
    obtain ⟨t, htε, hzt⟩ :=
      avram_p4_f19_strict_upclock_before_horizon_has_path_witness
        X z ε ω ht
    obtain ⟨r, _htr, hrε, hrpos⟩ :=
      avram_p4_f15_continuousWithin_positive_rational_witness
        (fun s => X.X s ω) t ε htε (lt_trans hz hzt)
        (X.rightCont ω t)
    exact ⟨r, hrε, hrpos⟩
  have hF (ω : Ω) :
      F ω ≤ A.indicator (fun _ : Ω => (1 : ℝ≥0∞)) ω + 1 / 4 := by
    have hs : F ω ≤ (if τ ω < (ε : ℝ≥0∞) then 1 else
      ENNReal.ofReal (Real.exp (-(q * (ε : ℝ))))) := by
      exact avram_p4_f18_discounted_finite_clock_split_le q hq.le ε (τ ω)
    rw [hb] at hs
    by_cases hω : ω ∈ A
    · simpa [Set.indicator_of_mem hω] using
        (hs.trans (by split_ifs <;> norm_num :
          (if τ ω < (ε : ℝ≥0∞) then (1 : ℝ≥0∞) else 1 / 4) ≤ 1 + 1 / 4))
    · have hnot : ¬ τ ω < (ε : ℝ≥0∞) := fun ht => hω (hτA ω ht)
      simpa [Set.indicator_of_notMem hω, hnot] using hs
  have hmean : (1 / 2 : ℝ≥0∞) = ∫⁻ ω, F ω ∂P := by
    rw [← hc]
    exact (levy_positive_root_exact_strict_upcrossing_discount
      X q hq φ hφ hroot z hz).symm
  have hupper : (∫⁻ ω, F ω ∂P) ≤ P A + 1 / 4 := by
    calc
      (∫⁻ ω, F ω ∂P) ≤
          ∫⁻ ω, A.indicator (fun _ : Ω => (1 : ℝ≥0∞)) ω + 1 / 4 ∂P :=
        lintegral_mono hF
      _ = P A + 1 / 4 := by
        rw [lintegral_add_left (measurable_const.indicator hA)]
        have hInd :
            (∫⁻ ω, A.indicator (fun _ : Ω => (1 : ℝ≥0∞)) ω ∂P) = P A := by
          simpa using (lintegral_indicator_const (μ := P) hA (1 : ℝ≥0∞))
        rw [hInd]
        simp [measure_univ]
  have hPA : (1 / 4 : ℝ≥0∞) ≤ P A := by
    have hquart : (1 / 4 : ℝ≥0∞) = ENNReal.ofReal (1 / 4 : ℝ) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
      norm_num
    have hhalf : (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2 : ℝ) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num
    have hh : (1 / 4 : ℝ≥0∞) + 1 / 4 ≤ P A + 1 / 4 := by
      calc
        (1 / 4 : ℝ≥0∞) + 1 / 4 = 1 / 2 := by
          rw [hquart, hhalf,
            ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 4)
              (by norm_num : (0 : ℝ) ≤ 1 / 4)]
          norm_num
        _ = ∫⁻ ω, F ω ∂P := hmean
        _ ≤ P A + 1 / 4 := hupper
    exact (ENNReal.add_le_add_iff_right (by norm_num : (1 / 4 : ℝ≥0∞) ≠ ⊤)).mp hh
  have hPAreal : (1 / 10 : ℝ) ≤ P.real A := by
    have hh := ENNReal.toReal_mono (measure_lt_top P A).ne hPA
    norm_num at hh ⊢
    exact le_trans (by norm_num : (1 / 10 : ℝ) ≤ 1 / 4) hh
  have hAE : A ⊆ {ω : Ω | ∃ s : ℝ≥0, s < ε ∧ 0 < X.X s ω} := by
    rintro ω ⟨r, hrε, hrpos⟩
    exact ⟨(r : ℝ≥0), hrε, hrpos⟩
  exact hPAreal.trans (measureReal_mono hAE)
