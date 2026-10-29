-- Prove2me | solution 1 for AvramDividend.Classical.ae_rogozin_slopes_of_infinite_small_jumps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T00:12:15.244158+00:00
-- url     : https://prove2.me/submissions/0c2100dd-ed37-4b6a-a116-e2e7d432149f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ae_rogozin_slopes_of_gaussian_component
import Theorems.Thm_AvramDividend_Classical_levy_linear_drift_shift_triplet_preserved_ws01f
import Theorems.Thm_AvramDividend_Classical_levy_infinite_jump_positive_factor_witnesses_ws01f
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_likelihood_joint_measurable_of_joint_levy_state
import Theorems.Thm_AvramDividend_Classical_levy_original_exp_clock_drawdown_zero_atom_of_infinite_jumps_ws01f
import Theorems.Thm_AvramDividend_Classical_levy_exp_clock_infimum_zero_atom_of_drawdown_ws01f
import Theorems.Thm_AvramDividend_Classical_levy_fixed_infimum_zero_atoms_of_exp_clock_ws01f
import Theorems.Thm_AvramDividend_Classical_levy_negative_near_zero_of_fixed_infimum_no_atom_ws01f
import Theorems.Thm_AvramDividend_Classical_frequently_negative_of_arbitrarily_small_negative_ws01f
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Filter Topology MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hjump : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤) :
    ∀ᵐ ω ∂P, ∀ C : ℝ,
      ∃ᶠ t in nhdsWithin (0 : ℝ≥0) (Ioi 0),
        X.X t ω < C * (t : ℝ) := by
  by_cases hσ : X.σ = 0
  · have hEach (k : ℕ) : ∀ᵐ ω ∂P,
        ∃ᶠ t in nhdsWithin (0 : ℝ≥0) (Ioi 0),
          X.X t ω < -(k : ℝ) * (t : ℝ) := by
      obtain ⟨Y, hYPath, hYPsi, hYSigma, hYNu⟩ :=
        levy_linear_drift_shift_triplet_preserved_ws01f
          X (-(k : ℝ))
      have hσY : Y.σ = 0 := by simpa [hYSigma] using hσ
      have hjumpY : (∫⁻ y in Ioo (-1 : ℝ) 0,
          ENNReal.ofReal |y| ∂Y.ν) = ⊤ := by
        simpa [hYNu] using hjump
      obtain ⟨q, φ, p, lam, m, hq, hφ, hroot, hp, hlam,
        hlamroot, hm, hmderiv⟩ :=
          levy_infinite_jump_positive_factor_witnesses_ws01f
            Y hσY hjumpY
      have hJoint :=
        chat04_esscher_likelihood_joint_measurable_of_joint_levy_state
          Y φ (chat04_levy_joint_time_state_measurable Y)
      have hD :=
        levy_original_exp_clock_drawdown_zero_atom_of_infinite_jumps_ws01f
          Y hjumpY q φ p lam m
          hq hφ hroot hp hlam hlamroot hm hmderiv hJoint
      have hI :=
        levy_exp_clock_infimum_zero_atom_of_drawdown_ws01f Y p hp hD
      have hFixed :=
        levy_fixed_infimum_zero_atoms_of_exp_clock_ws01f
          Y p hp hI
      have hSmall :=
        levy_negative_near_zero_of_fixed_infimum_no_atom_ws01f
          Y hFixed
      filter_upwards [hSmall] with ω hω
      have hFreq :=
        frequently_negative_of_arbitrarily_small_negative_ws01f
          (fun t => Y.X t ω) (Y.X_zero ω) hω
      apply hFreq.mono
      intro t ht
      have hPath := hYPath t ω
      linarith
    have hAll : ∀ᵐ ω ∂P, ∀ k : ℕ,
        ∃ᶠ t in nhdsWithin (0 : ℝ≥0) (Ioi 0),
          X.X t ω < -(k : ℝ) * (t : ℝ) :=
      ae_all_iff.mpr hEach
    filter_upwards [hAll] with ω hω
    intro C
    obtain ⟨k, hk⟩ := exists_nat_gt (-C)
    have hSlope : -(k : ℝ) < C := by linarith
    have hPos : ∀ᶠ t in nhdsWithin (0 : ℝ≥0) (Ioi 0), 0 < t := self_mem_nhdsWithin
    have hFrequent := (hω k).and_eventually hPos
    apply hFrequent.mono
    intro t ht
    have htime : 0 < (t : ℝ) := by exact_mod_cast ht.2
    exact lt_trans ht.1 (mul_lt_mul_of_pos_right hSlope htime)
  · have hσpos : 0 < X.σ := lt_of_le_of_ne X.σ_nonneg (Ne.symm hσ)
    exact ae_rogozin_slopes_of_gaussian_component X hσpos
