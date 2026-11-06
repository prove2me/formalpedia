-- Prove2me | solution 1 for BianchiIX.coreAngle_radius_drift
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:40:03.67334+00:00
-- url     : https://prove2.me/submissions/8d6809aa-9c4e-425b-9ac9-70bc58950d8c

import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Theorems.Thm_BianchiIX_abs_sub_le_integral_bound
import Theorems.Thm_BianchiIX_coreAngle_prefix_contraction
import Theorems.Thm_BianchiIX_core_four_integral_bounds
import Theorems.Thm_BianchiIX_core_radial_velocity_bound
import Theorems.Thm_BianchiIX_core_radius_budget
import Theorems.Thm_BianchiIX_sech_le_exp
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr

noncomputable section
open BianchiIX
open Set MeasureTheory


/-- Radius drift on every completed core prefix, with the coefficient in (A.9). -/
theorem solution {Y : ℝ → CoreAngleState} {a b k : ℝ}
    (hab : a ≤ b) (hk : 6 ≤ k)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (coreAngleField z (Y z)) z)
    (hinit : Y a 0 = k) (hentry : Real.cosh a = k)
    (hr : ∀ z ∈ Icc a b, 99 / 100 * k ≤ Y z 0 ∧ Y z 0 ≤ 101 / 100 * k)
    (hv : ∀ z ∈ Icc a b, 1 ≤ Y z 0 / Real.cosh z)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ (1 / 10000) / k)
    (hp : ∀ z ∈ Icc a b, 0 ≤ Y z 2 ∧ Y z 2 ≤ (1 / 10000) / k) :
    |Y b 0 - k| ≤ 16 / k * (Y a 1 + (Y a 2) ^ 2) := by
  let r : ℝ → ℝ := fun z => Y z 0
  let u : ℝ → ℝ := fun z => Y z 1
  let v : ℝ → ℝ := fun z => r z / Real.cosh z
  let w : ℝ → ℝ := fun z => Y z 2 / v z
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hk0 : 0 < k := by linarith
  have hr0 (z : ℝ) (hz : z ∈ Icc a b) : 0 < r z := by have H := (hr z hz).1; dsimp [r]; linarith
  have hv0 (z : ℝ) (hz : z ∈ Icc a b) : 0 < v z := lt_of_lt_of_le zero_lt_one (hv z hz)
  have hw (z : ℝ) (hz : z ∈ Icc a b) : 0 ≤ w z ∧ w z ≤ (1 / 10000) / k :=
    ⟨div_nonneg (hp z hz).1 (hv0 z hz).le, (div_le_self (hp z hz).1 (hv z hz)).trans (hp z hz).2⟩
  have hcon (z : ℝ) (hz : z ∈ Icc a b) :
      u z ≤ u a * Real.exp (-k * (z - a) / 4) ∧ Y z 2 ≤ Y a 2 := by
    exact coreAngle_prefix_contraction (z₀ := 0) (convex_Icc a b) hk
      (fun t ht => by simpa only [add_zero] using hY t ht)
      (fun t ht => (hr t ht).1) (by simpa only [add_zero] using hv) hu
      (by simpa only [add_zero] using hw) ha hz hz.1
  have hcoord (i : Fin 3) : ContinuousOn (fun z => Y z i) (Icc a b) :=
    fun z hz => (hasDerivAt_pi.mp (hY z hz) i).continuousAt.continuousWithinAt
  have hrc : ContinuousOn r (Icc a b) := hcoord 0
  have huc : ContinuousOn u (Icc a b) := hcoord 1
  have hvc : ContinuousOn v (Icc a b) := hrc.div Real.continuous_cosh.continuousOn
    (fun z _ => ne_of_gt (Real.cosh_pos z))
  have hwc : ContinuousOn w (Icc a b) := (hcoord 2).div hvc (fun z hz => ne_of_gt (hv0 z hz))
  have hlo (z : ℝ) (hz : z ∈ Icc a b) : 9 / 10 * k ≤ r z := by have H := (hr z hz).1; dsimp [r]; linarith
  have hvexp (z : ℝ) (hz : z ∈ Icc a b) : 0 ≤ v z ∧ v z ≤ (11 / 10) * Real.exp (z - a) := by
    refine ⟨(hv0 z hz).le, ?_⟩
    have H := sech_le_exp hz.1
    rw [hentry] at H
    calc
      v z = r z * (1 / Real.cosh z) := by dsimp [v]; ring
      _ ≤ (11 / 10 * k) * ((1 / k) * Real.exp (z - a)) :=
        mul_le_mul (by have H := (hr z hz).2; dsimp [r]; linarith) H (by positivity) (by positivity)
      _ = (11 / 10) * Real.exp (z - a) := by field_simp
  have hwenv (z : ℝ) (hz : z ∈ Icc a b) :
      0 ≤ w z ∧ w z ≤ Y a 2 ∧ w z ≤ Y a 2 * Real.cosh z / r z := by
    refine ⟨(hw z hz).1, (div_le_self (hp z hz).1 (hv z hz)).trans (hcon z hz).2, ?_⟩
    calc
      w z = Y z 2 * Real.cosh z / r z := by
        dsimp [w, v]
        field_simp [ne_of_gt (hr0 z hz), ne_of_gt (Real.cosh_pos z)]
      _ ≤ Y a 2 * Real.cosh z / r z :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hcon z hz).2 (Real.cosh_pos z).le) (hr0 z hz).le
  have hend (z : ℝ) (hz : z ∈ Icc a b) : Real.cosh z ≤ 11 / 10 * k := by
    have H := (le_div_iff₀ (Real.cosh_pos z)).mp (hv z hz)
    have H' := (hr z hz).2
    nlinarith
  obtain ⟨hUV, hUW, hU2, hW2⟩ := core_four_integral_bounds hab hk (hu a ha).1 (hp a ha).1
    hrc huc hvc hwc hlo (fun z hz => ⟨(hu z hz).1, (hcon z hz).1⟩) hvexp hwenv (hend a ha) (hend b hb)
  have hc1 := huc.mul hvc
  have hc2 := huc.mul hwc
  have hc3 := (huc.pow 2).div hrc (fun z hz => ne_of_gt (hr0 z hz))
  have hc4 := (hwc.pow 2).div hrc (fun z hz => ne_of_gt (hr0 z hz))
  have hbound (z : ℝ) (hz : z ∈ Icc a b) :
      |coreAngleField z (Y z) 0| ≤ (u z * v z + u z * w z + u z ^ 2 / r z + w z ^ 2 / r z) / (999 / 1000) :=
    core_radial_velocity_bound hk (hr z hz).1 (hv z hz) (hu z hz) (hw z hz) (Real.abs_tanh_lt_one z).le
  have H := abs_sub_le_integral_bound hab (fun z hz => hasDerivAt_pi.mp (hY z hz) 0)
    (((hc1.add hc2).add hc3).add hc4 |>.div_const (999 / 1000)) hbound
  have hi1 := hc1.intervalIntegrable_of_Icc (μ := volume) hab
  have hi2 := hc2.intervalIntegrable_of_Icc (μ := volume) hab
  have hi3 := hc3.intervalIntegrable_of_Icc (μ := volume) hab
  have hi4 := hc4.intervalIntegrable_of_Icc (μ := volume) hab
  rw [hinit, intervalIntegral.integral_div] at H
  simp only [Pi.add_apply] at H
  rw [
    intervalIntegral.integral_add ((hi1.add hi2).add hi3) hi4,
    intervalIntegral.integral_add (hi1.add hi2) hi3, intervalIntegral.integral_add hi1 hi2] at H
  apply H.trans
  apply (div_le_div_of_nonneg_right (add_le_add (add_le_add (add_le_add hUV hUW) hU2) hW2)
    (by norm_num : (0 : ℝ) ≤ 999 / 1000)).trans
  exact core_radius_budget hk (hu a ha) (hp a ha)
