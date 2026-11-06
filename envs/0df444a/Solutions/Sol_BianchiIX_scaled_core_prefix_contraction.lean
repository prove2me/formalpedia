-- Prove2me | solution 1 for BianchiIX.scaled_core_prefix_contraction
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:06:09.59713+00:00
-- url     : https://prove2.me/submissions/12aa07b1-da65-4a00-8daf-83bac85728be

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Theorems.Thm_BianchiIX_coreAngleField_product_nonpos
import Theorems.Thm_BianchiIX_coreAngleField_strong_le
import Theorems.Thm_BianchiIX_coreBootstrap_clock_bounds
import Theorems.Thm_BianchiIX_hasDerivAt_coreAngle_scaled
import Theorems.Thm_BianchiIX_hasDerivAt_toCoreAngleState_scaled
import Theorems.Thm_BianchiIX_le_exp_of_clock_deriv_le
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

private theorem BianchiIX.coreRadius_pos {m v : ℝ} (hv : 0 < v) : 0 < coreRadius m v := by
  apply Real.sqrt_pos.mpr
  unfold coreEnergy
  positivity

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreAngle_sqrt {m v : ℝ} (hv : 0 < v) :
    Real.sqrt (1 + ((1 - m) / v) ^ 2) = coreRadius m v / v := by
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (div_nonneg (coreRadius_pos hv).le hv.le)).mpr
  simp only [div_pow, coreRadius_sq]
  unfold coreEnergy
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.cosh_coreAngle {m v : ℝ} (hv : 0 < v) :
    Real.cosh (coreAngle m v) = coreRadius m v / v := by
  rw [coreAngle, Real.cosh_arsinh, coreAngle_sqrt hv]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.tanh_coreAngle {m v : ℝ} (hv : 0 < v) :
    Real.tanh (coreAngle m v) = (1 - m) / coreRadius m v := by
  rw [coreAngle, Real.tanh_arsinh, coreAngle_sqrt hv]
  field_simp

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreAngle_coordinates {m v : ℝ} (hv : 0 < v) :
    coreRadius m v / Real.cosh (coreAngle m v) = v ∧
      1 - coreRadius m v * Real.tanh (coreAngle m v) = m := by
  have hr := ne_of_gt (coreRadius_pos (m := m) hv)
  rw [cosh_coreAngle hv, tanh_coreAngle hv]
  constructor
  · field_simp
  · field_simp
    ring

end
end

/-- The prefix estimates expressed directly in the physical projective state. -/
theorem solution {β : ℝ → ProjectiveState} {a : ℝ → ℝ}
    {I : Set ℝ} {k s t : ℝ} (hk : 6 ≤ k) (hI : Convex ℝ I)
    (ha_pos : ∀ u ∈ I, 0 < a u)
    (hβ : ∀ u ∈ I, HasDerivAt β (a u • projectiveField (β u)) u)
    (hr : ∀ u ∈ I, 99 / 100 * k ≤ coreRadius (β u 0) (β u 2))
    (hv : ∀ u ∈ I, 1 ≤ β u 2)
    (hu : ∀ z ∈ I, 0 ≤ β z 1 ∧ β z 1 ≤ (1 / 10000) / k)
    (hw : ∀ z ∈ I, 0 ≤ β z 3 ∧ β z 3 ≤ (1 / 10000) / k)
    (hs : s ∈ I) (ht : t ∈ I) (hst : s ≤ t) :
    β t 1 ≤ β s 1 * Real.exp (-k * (coreAngle (β t 0) (β t 2) - coreAngle (β s 0) (β s 2)) / 4) ∧
      β t 2 * β t 3 ≤ β s 2 * β s 3 := by
  have hvpos : ∀ u ∈ I, 0 < β u 2 := fun u hh => lt_of_lt_of_le zero_lt_one (hv u hh)
  have hd : ∀ u ∈ I, 0 < coreClockFactor (coreRadius (β u 0) (β u 2)) (β u 1) (β u 3) :=
    fun u hh => lt_of_lt_of_le (by norm_num : (0 : ℝ) < 999 / 1000)
      (coreBootstrap_clock_bounds hk (hr u hh) (hu u hh) (hw u hh)).1
  let q : ℝ → ℝ := fun u => a u * coreRadius (β u 0) (β u 2) *
    coreClockFactor (coreRadius (β u 0) (β u 2)) (β u 1) (β u 3)
  let F : ℝ → CoreAngleState := fun u => coreAngleField (coreAngle (β u 0) (β u 2)) (toCoreAngleState (β u))
  have hq : ∀ u ∈ I, 0 < q u := fun u hh =>
    mul_pos (mul_pos (ha_pos u hh) (coreRadius_pos (hvpos u hh))) (hd u hh)
  have hstate (u : ℝ) (hh : u ∈ I) :
      HasDerivAt (fun v => toCoreAngleState (β v)) (q u • F u) u :=
    hasDerivAt_toCoreAngleState_scaled (hβ u hh) (hvpos u hh) (ne_of_gt (hd u hh))
  have hF (u : ℝ) (hh : u ∈ I) : F u 1 ≤ (-k / 4) * β u 1 ∧ F u 2 ≤ 0 := by
    have hV : toCoreAngleState (β u) 0 / Real.cosh (coreAngle (β u 0) (β u 2)) = β u 2 :=
      (coreAngle_coordinates (hvpos u hh)).1
    have hW : toCoreAngleState (β u) 2 /
        (toCoreAngleState (β u) 0 / Real.cosh (coreAngle (β u 0) (β u 2))) = β u 3 := by
      rw [hV]
      change β u 2 * β u 3 / β u 2 = _
      field_simp [ne_of_gt (hvpos u hh)]
    have hw' : 0 ≤ toCoreAngleState (β u) 2 /
        (toCoreAngleState (β u) 0 / Real.cosh (coreAngle (β u 0) (β u 2))) ∧
        toCoreAngleState (β u) 2 /
        (toCoreAngleState (β u) 0 / Real.cosh (coreAngle (β u 0) (β u 2))) ≤ (1 / 10000) / k := by
      rw [hW]
      exact hw u hh
    exact ⟨coreAngleField_strong_le hk (hr u hh) (hu u hh) hw',
      coreAngleField_product_nonpos hk (hr u hh) (by rw [hV]; exact hv u hh) (hu u hh) hw'⟩
  constructor
  · have H := le_exp_of_clock_deriv_le hI (c := -k / 4)
      (fun u hh => hasDerivAt_pi.mp (hstate u hh) 1)
      (fun u hh => hasDerivAt_coreAngle_scaled (hβ u hh) (hvpos u hh))
      (fun u hh => (mul_le_mul_of_nonneg_left (hF u hh).1 (hq u hh).le).trans_eq
        (by dsimp [q, toCoreAngleState]; ring)) hs ht hst
    convert! H using 1
    congr 2
    ring
  · have hanti : AntitoneOn (fun u => toCoreAngleState (β u) 2) I := antitoneOn_of_deriv_nonpos hI
      (fun u hh => (hasDerivAt_pi.mp (hstate u hh) 2).continuousAt.continuousWithinAt)
      (fun u hh => (hasDerivAt_pi.mp (hstate u (interior_subset hh)) 2).differentiableAt.differentiableWithinAt)
      (fun u hh => by
        rw [(hasDerivAt_pi.mp (hstate u (interior_subset hh)) 2).deriv]
        exact mul_nonpos_of_nonneg_of_nonpos (hq u (interior_subset hh)).le (hF u (interior_subset hh)).2)
    exact hanti hs ht hst
