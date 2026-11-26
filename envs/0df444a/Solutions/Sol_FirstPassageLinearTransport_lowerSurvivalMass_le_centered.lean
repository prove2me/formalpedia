-- Prove2me | solution 1 for FirstPassageLinearTransport.lowerSurvivalMass_le_centered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:54:21.099829+00:00
-- url     : https://prove2.me/submissions/8c4bade4-0e4a-446c-a0a6-2d0d02412077

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_lowerSurvivalMass_le_centered_explicit

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {p v h : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hv : 0 < v) (hh : 0 ≤ h)
    {x : Bool → ℝ} (hx : ∀ b, |x b| ≤ 1)
    (hcenter : bernoulliAverage p (x false) (x true) = 0)
    (hvariance : bernoulliAverage p ((x false) ^ 2) ((x true) ^ 2) = v)
    {n : ℕ} (hn : 0 < n) :
    lowerSurvivalMass p x (-h) n 0 ≤
      (1 + 2 / v) * (h + 1) / Real.sqrt n := by
  have hexplicit := lowerSurvivalMass_le_centered_explicit
    hp₀ hp₁ hv hh hx hcenter hvariance hn
  have hnR : 0 < (n : ℝ) := by positivity
  have hsqrtPos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hsqrtOne : 1 ≤ Real.sqrt (n : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
  have hfirst :
      (h + 1) / (Real.sqrt n + h + 1) ≤
        (h + 1) / Real.sqrt n := by
    exact div_le_div_of_nonneg_left (by linarith) hsqrtPos (by linarith)
  have hsquare : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt hnR.le
  have hratio :
      (Real.sqrt n + 1) / (n : ℝ) ≤ 2 / Real.sqrt n := by
    apply (div_le_div_iff₀ hnR hsqrtPos).2
    nlinarith
  have hfactor : 0 ≤ (h + 1) / v := by positivity
  have hsecond :
      (h + 1) * (Real.sqrt n + 1) / (v * n) ≤
        (2 / v) * (h + 1) / Real.sqrt n := by
    calc
      (h + 1) * (Real.sqrt n + 1) / (v * n) =
          ((h + 1) / v) * ((Real.sqrt n + 1) / n) := by
        field_simp [hv.ne', hnR.ne']
      _ ≤ ((h + 1) / v) * (2 / Real.sqrt n) :=
        mul_le_mul_of_nonneg_left hratio hfactor
      _ = (2 / v) * (h + 1) / Real.sqrt n := by ring
  calc
    lowerSurvivalMass p x (-h) n 0 ≤
        (h + 1) / (Real.sqrt n + h + 1) +
          (h + 1) * (Real.sqrt n + 1) / (v * n) := hexplicit
    _ ≤ (h + 1) / Real.sqrt n +
        (2 / v) * (h + 1) / Real.sqrt n := add_le_add hfirst hsecond
    _ = (1 + 2 / v) * (h + 1) / Real.sqrt n := by ring
end FirstPassageLinearTransport
