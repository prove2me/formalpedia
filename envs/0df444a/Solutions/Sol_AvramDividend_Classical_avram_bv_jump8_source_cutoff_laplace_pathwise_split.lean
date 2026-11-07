-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_source_cutoff_laplace_pathwise_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:42:38.918879+00:00
-- url     : https://prove2.me/submissions/047a8ce3-f803-4df8-a988-5aa7edc5061a

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_halfopen_marked_exponential_factor_of_finite
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_original_cutoff_weighted_lintegral_finite_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Actual intrinsic marks have multiplicative finite-cutoff Laplace weights on adjacent windows. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (n k : ℕ),
      Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
        if 0 < p.1 ∧ p.1 ≤ ((n + 1) : ℝ≥0) ∧
            p.2 < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-p.2) else 0 ∂
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal)) =
      Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
        if 0 < p.1 ∧ p.1 ≤ (n : ℝ≥0) ∧
            p.2 < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-p.2) else 0 ∂
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal)) * Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
        if (n : ℝ≥0) < p.1 ∧ p.1 ≤ ((n + 1) : ℝ≥0) ∧
            p.2 < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-p.2) else 0 ∂
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal)) := by
  filter_upwards [avram_bv_jump8_original_cutoff_weighted_lintegral_finite_ae X hBV] with ω hω
  intro n k
  let μ : Measure (ℝ≥0 × ℝ) := ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let g : ℝ≥0 × ℝ → ℝ≥0∞ := (fun p : ℝ≥0 × ℝ => if p.2 < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-p.2) else 0)
  have hg : Measurable g := by
    dsimp [g]
    have hset : MeasurableSet {p : ℝ≥0 × ℝ | p.2 < -(1 / ((k : ℝ) + 1))} :=
      measurableSet_lt measurable_snd measurable_const
    have hval : Measurable (fun p : ℝ≥0 × ℝ => ENNReal.ofReal (-p.2)) := by
      fun_prop
    exact hval.ite hset measurable_const
  have hLeft : (∫⁻ p : ℝ≥0 × ℝ, if 0 < p.1 ∧ p.1 ≤ (n : ℝ≥0) then g p else 0 ∂μ) ≠ ∞ := by
    simpa only [μ, g, ite_and] using hω (n : ℝ≥0) k
  have hFull : (∫⁻ p : ℝ≥0 × ℝ, if 0 < p.1 ∧ p.1 ≤ ((n + 1 : ℕ) : ℝ≥0) then g p else 0 ∂μ) ≠ ∞ := by
    simpa only [μ, g, ite_and] using hω ((n + 1 : ℕ) : ℝ≥0) k
  have hRightLe : (∫⁻ p : ℝ≥0 × ℝ, if (n : ℝ≥0) < p.1 ∧ p.1 ≤ ((n + 1 : ℕ) : ℝ≥0) then g p else 0 ∂μ) ≤ (∫⁻ p : ℝ≥0 × ℝ, if 0 < p.1 ∧ p.1 ≤ ((n + 1 : ℕ) : ℝ≥0) then g p else 0 ∂μ) := by
    apply lintegral_mono
    intro p
    by_cases ht : (n : ℝ≥0) < p.1 ∧ p.1 ≤ ((n + 1 : ℕ) : ℝ≥0)
    · have h0 : 0 < p.1 ∧ p.1 ≤ ((n + 1 : ℕ) : ℝ≥0) :=
        ⟨lt_of_le_of_lt (show (0 : ℝ≥0) ≤ (n : ℝ≥0) from bot_le) ht.1, ht.2⟩
      simp only [if_pos ht, if_pos h0, le_refl]
    · simp only [if_neg ht]
      exact bot_le
  have hRight : (∫⁻ p : ℝ≥0 × ℝ, if (n : ℝ≥0) < p.1 ∧ p.1 ≤ ((n + 1 : ℕ) : ℝ≥0) then g p else 0 ∂μ) ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt hRightLe (lt_top_iff_ne_top.mpr hFull))
  have hBound : (n : ℝ≥0) ≤ ((n + 1 : ℕ) : ℝ≥0) := by exact_mod_cast Nat.le_succ n
  have hFactor :=
    avram_bv_jump8_halfopen_marked_exponential_factor_of_finite
      μ g hg (n : ℝ≥0) ((n + 1 : ℕ) : ℝ≥0) hBound hLeft hRight
  simpa only [μ, g, ite_and, Nat.cast_add, Nat.cast_one] using hFactor
