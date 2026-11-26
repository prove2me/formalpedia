-- Prove2me | solution 1 for FirstPassageLinearTransport.lowerSurvivalMass_le_centered_explicit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:53:31.837594+00:00
-- url     : https://prove2.me/submissions/985a2f49-d1ca-4f8e-8f40-7020aba48ddc

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_stoppedWalkMean_eq
import Theorems.Thm_FirstPassageLinearTransport_stoppedWalkSecond_eq
import Theorems.Thm_FirstPassageLinearTransport_stoppedWalkMoment_upper
import Theorems.Thm_FirstPassageLinearTransport_stoppedUpperMass_mean_lower
import Theorems.Thm_FirstPassageLinearTransport_stoppedHorizonMass_mul_le_time
import Theorems.Thm_FirstPassageLinearTransport_lowerSurvivalMass_le_stopped_split
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



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
      (h + 1) / (Real.sqrt n + h + 1) +
        (h + 1) * (Real.sqrt n + 1) / (v * n) := by
  have hnR : 0 < (n : ℝ) := by positivity
  have hsqrtPos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hlohi : -h ≤ Real.sqrt (n : ℝ) := by
    exact le_trans (neg_nonpos.mpr hh) (Real.sqrt_nonneg _)
  let upper := stoppedUpperMass p x (-h) (Real.sqrt n) n 0
  let horizon := stoppedHorizonMass p x (-h) (Real.sqrt n) n 0
  let time := stoppedWalkTime p x (-h) (Real.sqrt n) n 0
  have hmean := stoppedWalkMean_eq x (-h) (Real.sqrt n) hcenter n 0
  have hupperMoment := stoppedUpperMass_mean_lower hp₀ hp₁ hx hlohi n 0 (by linarith)
  have hupperLinear :
      (Real.sqrt n + h + 1) * upper ≤ h + 1 := by
    dsimp [upper]
    rw [hmean] at hupperMoment
    nlinarith
  have hdenPos : 0 < Real.sqrt n + h + 1 := by positivity
  have hupper : upper ≤ (h + 1) / (Real.sqrt n + h + 1) :=
    (le_div_iff₀ hdenPos).2 (by simpa [mul_comm] using hupperLinear)
  have hsecond := stoppedWalkSecond_eq x (-h) (Real.sqrt n)
    hcenter hvariance n (0 : ℝ)
  have hmoment := stoppedWalkMoment_upper hp₀ hp₁ hx
    (lo := -h) (hi := Real.sqrt n) n (0 : ℝ)
    (by linarith)
    (by have hs := Real.sqrt_nonneg (n : ℝ); linarith)
  have htimeLinear : v * time ≤ (h + 1) * (Real.sqrt n + 1) := by
    dsimp [time]
    rw [hsecond, hmean] at hmoment
    nlinarith
  have htime : time ≤ (h + 1) * (Real.sqrt n + 1) / v :=
    (le_div_iff₀ hv).2 (by simpa [mul_comm] using htimeLinear)
  have hhorizonMul := stoppedHorizonMass_mul_le_time hp₀ hp₁
    x (-h) (Real.sqrt n) n 0
  have hhorizon :
      horizon ≤ (h + 1) * (Real.sqrt n + 1) / (v * n) := by
    calc
      horizon ≤ time / (n : ℝ) := by
        exact (le_div_iff₀ hnR).2
          (by simpa [horizon, time, mul_comm] using hhorizonMul)
      _ ≤ ((h + 1) * (Real.sqrt n + 1) / v) / (n : ℝ) :=
        div_le_div_of_nonneg_right htime hnR.le
      _ = (h + 1) * (Real.sqrt n + 1) / (v * n) := by
        field_simp [hv.ne', hnR.ne']
  have hsplit := lowerSurvivalMass_le_stopped_split hp₀ hp₁
    x (-h) (Real.sqrt n) n 0
  exact hsplit.trans (add_le_add hupper hhorizon)
end FirstPassageLinearTransport
