-- Prove2me | solution 2 for CohnElkies.realHyperbolicShellPhase_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:56:51.028772+00:00
-- url     : https://prove2.me/submissions/f52f0c04-6f38-40f0-96c1-741d3c8f5e06

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
theorem h48_hasDeriv (ρ : ℝ → ℝ) (x y : ℝ) (hρ : IntervalIntegrable ρ volume x y) (u : ℝ) :
    HasDerivAt (fun v => ∫ a in x..y, ρ a * (Real.cosh (a * v) - 1))
      (∫ a in x..y, ρ a * a * Real.sinh (a * u)) u := by
  set M : ℝ := max |x| |y| with hM
  have hρm : AEStronglyMeasurable ρ (volume.restrict (Set.uIoc x y)) := hρ.def'.aestronglyMeasurable
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun v a => ρ a * (Real.cosh (a * v) - 1))
    (F' := fun v a => ρ a * a * Real.sinh (a * v)) (x₀ := u) (μ := volume) (a := x) (b := y)
    (s := Set.Ioo (u - 1) (u + 1))
    (bound := fun a => |ρ a| * (M * Real.cosh (M * (|u| + 1))))
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Filter.Eventually.of_forall (fun v => hρm.mul (Continuous.aestronglyMeasurable (f := fun a : ℝ => Real.cosh (a * v) - 1) (by fun_prop))))
    (hρ.mul_continuousOn (Continuous.continuousOn (f := fun a : ℝ => Real.cosh (a * u) - 1) (by fun_prop)))
    ((hρm.mul (Continuous.aestronglyMeasurable (f := fun a : ℝ => a) (by fun_prop))).mul
      (Continuous.aestronglyMeasurable (f := fun a : ℝ => Real.sinh (a * u)) (by fun_prop)))
    ?_ (hρ.abs.mul_const _) ?_
  · exact key.2
  · refine Filter.Eventually.of_forall (fun t ht v hv => ?_)
    have htM : |t| ≤ M := by
      rcases Set.uIoc_subset_uIcc ht with h
      rw [Set.mem_uIcc] at h
      rcases h with h | h
      · exact abs_le_max_abs_abs h.1 h.2
      · rw [hM, max_comm]; exact abs_le_max_abs_abs h.1 h.2
    have hvu : |v| ≤ |u| + 1 := by
      have : |v - u| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hv.1, hv.2]
      have := abs_sub_abs_le_abs_sub v u
      linarith
    have hM0 : 0 ≤ M := (abs_nonneg x).trans (le_max_left _ _)
    have h1 : |Real.sinh (t * v)| ≤ Real.cosh (M * (|u| + 1)) := by
      rw [Real.abs_sinh]
      refine (Real.sinh_lt_cosh _).le.trans ?_
      rw [Real.cosh_le_cosh, abs_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ M * (|u| + 1))]
      exact mul_le_mul htM hvu (abs_nonneg _) hM0
    simp only [Real.norm_eq_abs, abs_mul]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul htM h1 (abs_nonneg _) hM0) (abs_nonneg _)
  · refine Filter.Eventually.of_forall (fun t _ v _ => ?_)
    have h := (((hasDerivAt_id v).const_mul t).cosh.sub_const 1).const_mul (ρ t)
    simp only [id] at h
    refine h.congr_deriv ?_
    ring

theorem solution
    {ε : ℝ}
    (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (u : ℝ) :
    HasDerivAt (realHyperbolicShellPhase ε)
      ((∫ a in shortCutoff ε..shortEndpoint ε,
          shortShellDensity ε a * a * Real.sinh (a * u)) +
       (∫ a in shellLocation ε..shellLocation ε + 1,
          positiveShellDensity ε a * a * Real.sinh (a * u))) u := by
  have hs := shortShellDensity_intervalIntegrable hε horder
  have hp : IntervalIntegrable (positiveShellDensity ε) volume
      (shellLocation ε) (shellLocation ε + 1) :=
    (positiveShellDensity_continuous ε).intervalIntegrable _ _
  have h := (h48_hasDeriv _ _ _ hs u).add (h48_hasDeriv _ _ _ hp u)
  unfold realHyperbolicShellPhase
  exact h

