-- Prove2me | solution 1 for BianchiIX.scaled_core_exit_contraction
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:37:30.755869+00:00
-- url     : https://prove2.me/submissions/ba5fe979-7e31-435c-bcea-205861d89236

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Theorems.Thm_BianchiIX_coreBootstrap_phase_velocity
import Theorems.Thm_BianchiIX_image_sub_le_clock_sub_of_deriv_le
import Theorems.Thm_BianchiIX_scaled_core_amplitude_decay
import Theorems.Thm_BianchiIX_scaled_core_return_downward
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreRadius_sq (m v : ℝ) : coreRadius m v ^ 2 = coreEnergy m v :=
  Real.sq_sqrt (by unfold coreEnergy; positivity)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreRadius_component_bounds (m v : ℝ) :
    |m - 1| ≤ coreRadius m v ∧ |v| ≤ coreRadius m v := by
  have hr : 0 ≤ coreRadius m v := Real.sqrt_nonneg _
  have he := coreRadius_sq m v
  unfold coreEnergy at he
  constructor
  · apply (sq_le_sq₀ (abs_nonneg _) hr).mp
    rw [sq_abs]
    nlinarith [sq_nonneg v]
  · apply (sq_le_sq₀ (abs_nonneg _) hr).mp
    rw [sq_abs]
    nlinarith [sq_nonneg (m - 1)]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.core_section_phase_gap {k m : ℝ} (hk : 6 ≤ k)
    (hr : 99 / 100 * k ≤ coreRadius m 1) : 3 * k / 4 ≤ |m - 1| := by
  have hr2 := (sq_le_sq₀ (by linarith : 0 ≤ 99 / 100 * k)
    (show 0 ≤ coreRadius m 1 from Real.sqrt_nonneg _)).mpr hr
  rw [coreRadius_sq] at hr2
  unfold coreEnergy at hr2
  apply (sq_le_sq₀ (by linarith : 0 ≤ 3 * k / 4) (abs_nonneg _)).mp
  rw [sq_abs]
  nlinarith [sq_nonneg (k - 6)]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreBootstrap_phase_bound {k m v : ℝ} (hk : 6 ≤ k)
    (hr : coreRadius m v ≤ 101 / 100 * k) : |m| ≤ 6 / 5 * k := by
  have H := (coreRadius_component_bounds m v).1.trans hr
  calc
    |m| = |(m - 1) + 1| := by congr 1; ring
    _ ≤ |m - 1| + |(1 : ℝ)| := abs_add_le _ _
    _ ≤ 6 / 5 * k := by norm_num at *; linarith

end
end

/-- The phase displacement forces a positive projective duration and both exit contractions. -/
theorem solution {β : ℝ → ProjectiveState} {a τ : ℝ → ℝ}
    {k s t : ℝ} (hk : 6 ≤ k) (hst : s < t)
    (ha : ∀ u ∈ Icc s t, 0 < a u)
    (hβ : ∀ u ∈ Icc s t, HasDerivAt β (a u • projectiveField (β u)) u)
    (hτ : ∀ u ∈ Icc s t, HasDerivAt τ (a u) u)
    (hr : ∀ u ∈ Icc s t, 99 / 100 * k ≤ coreRadius (β u 0) (β u 2) ∧
      coreRadius (β u 0) (β u 2) ≤ 101 / 100 * k)
    (hv : ∀ u ∈ Icc s t, 1 ≤ β u 2)
    (hu : ∀ u ∈ Icc s t, 0 ≤ β u 1 ∧ β u 1 ≤ (1 / 10000) / k)
    (hw : ∀ u ∈ Icc s t, 0 ≤ β u 3 ∧ β u 3 ≤ (1 / 10000) / k)
    (hvs : β s 2 = 1) (hvt : β t 2 = 1) (hms : 1 ≤ β s 0) :
    1 / (4 * k) ≤ τ t - τ s ∧
      β t 1 ≤ Real.exp (-k / 40) * β s 1 ∧
      β t 3 ≤ Real.exp (-1 / (2 * k)) * β s 3 := by
  have hs : s ∈ Icc s t := ⟨le_rfl, hst.le⟩
  have ht : t ∈ Icc s t := ⟨hst.le, le_rfl⟩
  have hk0 : 0 < k := by linarith
  have hout := scaled_core_return_downward hk hst (ha t ht) (hβ t ht) hvt
    (fun u hh => hv u ⟨hh.1.le, hh.2.le⟩) (hr t ht).1 (hu t ht) (hw t ht)
  have hgs := core_section_phase_gap hk (by simpa only [hvs] using (hr s hs).1)
  have hgt := core_section_phase_gap hk (by simpa only [hvt] using (hr t ht).1)
  rw [abs_of_nonneg (sub_nonneg.mpr hms)] at hgs
  rw [abs_of_neg (by linarith [hout.1] : β t 0 - 1 < 0)] at hgt
  have hspeed (u : ℝ) (hh : u ∈ Icc s t) : -phaseVelocity (β u 0) (β u 1) (β u 2) (β u 3) ≤ 4 * k ^ 2 := by
    have H := (coreBootstrap_phase_velocity hk (coreBootstrap_phase_bound hk (hr u hh).2)
      (hv u hh) (hu u hh) (hw u hh)).2
    have hvhi : β u 2 ≤ 101 / 100 * k :=
      (le_abs_self _).trans ((coreRadius_component_bounds _ _).2.trans (hr u hh).2)
    have hv2 := (sq_le_sq₀ (by linarith [hv u hh]) (by positivity : 0 ≤ 101 / 100 * k)).mpr hvhi
    nlinarith [sq_nonneg k]
  have hdisp := image_sub_le_clock_sub_of_deriv_le (convex_Icc s t)
    (fun u hh => (hasDerivAt_pi.mp (hβ u hh) 0).neg) hτ
    (C := 4 * k ^ 2) (fun u hh => by
      have H := mul_le_mul_of_nonneg_left (hspeed u hh) (ha u hh).le
      change -(a u * phaseVelocity (β u 0) (β u 1) (β u 2) (β u 3)) ≤ _
      nlinarith) hs ht hst.le
  have htime : 1 / (4 * k) ≤ τ t - τ s := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * k)).mpr
    have H : k * 1 ≤ k * ((τ t - τ s) * (4 * k)) := by dsimp at hdisp; nlinarith
    exact le_of_mul_le_mul_left H hk0
  obtain ⟨hU, hP⟩ := scaled_core_amplitude_decay hk (convex_Icc s t) (fun u hh => (ha u hh).le)
    hβ hτ hr hv hu hw hs ht hst.le
  have hUexp : (-k ^ 2 / 10) * (τ t - τ s) ≤ -k / 40 := by
    calc
      _ ≤ (-k ^ 2 / 10) * (1 / (4 * k)) := mul_le_mul_of_nonpos_left htime (by nlinarith [sq_nonneg k])
      _ = _ := by field_simp; ring
  have hPexp : -2 * (τ t - τ s) ≤ -1 / (2 * k) := by
    calc
      _ ≤ -2 * (1 / (4 * k)) := mul_le_mul_of_nonpos_left htime (by norm_num)
      _ = _ := by field_simp; ring
  rw [hvs, hvt, one_mul, one_mul] at hP
  refine ⟨htime, ?_, ?_⟩
  · exact hU.trans ((mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hUexp) (hu s hs).1).trans_eq (mul_comm _ _))
  · exact hP.trans ((mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hPexp) (hw s hs).1).trans_eq (mul_comm _ _))
