-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva22_original_nojump_U_horizon_mask_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:33:12.484617+00:00
-- url     : https://prove2.me/submissions/fc244dda-5f3b-492d-bdaf-cb39b88063eb

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva22_original_physical_U_eq_measurable_leftdividend_proxy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original zero-jump physical reserve has a measurable positive-horizon mask. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (S : ℝ≥0)
    (hsource : ∀ r : ℝ≥0, r ≤ S → X.X r ω = (r : ℝ) * X.drift)
    (hLeft : Measurable (fun t : ℝ≥0 =>
      Function.leftLim (fun r : ℝ≥0 => rightLimit D r ω) t)) :
    Measurable (fun t : ℝ≥0 =>
      if 0 < t ∧ t ≤ S then
        Function.leftLim (fun r : ℝ≥0 =>
          x + X.X r ω - rightLimit D r ω) t
      else 0) := by
  classical
  let V : ℝ≥0 → ℝ := fun t =>
    x + (t : ℝ) * X.drift -
      Function.leftLim (fun r : ℝ≥0 => rightLimit D r ω) t
  have hV : Measurable V := by
    dsimp [V]
    fun_prop
  have hB : MeasurableSet {t : ℝ≥0 | 0 < t ∧ t ≤ S} :=
    measurableSet_Ioi.inter measurableSet_Iic
  have hPiece : Measurable (fun t : ℝ≥0 =>
      if 0 < t ∧ t ≤ S then V t else 0) :=
    hV.ite hB measurable_const
  have hEq : (fun t : ℝ≥0 =>
      if 0 < t ∧ t ≤ S then
        Function.leftLim (fun r : ℝ≥0 =>
          x + X.X r ω - rightLimit D r ω) t else 0) =
      (fun t : ℝ≥0 => if 0 < t ∧ t ≤ S then V t else 0) := by
    funext t
    by_cases ht : 0 < t ∧ t ≤ S
    · simp only [if_pos ht]
      exact avram_bva22_original_physical_U_eq_measurable_leftdividend_proxy
        X x C D hD ω S t ht.2 ht.1 hsource
    · simp [ht]
  rw [hEq]
  exact hPiece
