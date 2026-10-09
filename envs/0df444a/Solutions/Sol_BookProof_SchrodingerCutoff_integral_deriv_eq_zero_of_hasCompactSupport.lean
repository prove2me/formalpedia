-- Prove2me | solution 1 for BookProof.SchrodingerCutoff.integral_deriv_eq_zero_of_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T14:50:34.959244+00:00
-- url     : https://prove2.me/submissions/d209141e-0be1-4c86-8787-ae3c68579d2c

-- Generated from ChapterSchrodingerCutoffEsa.lean — solution of BookProof.SchrodingerCutoff.integral_deriv_eq_zero_of_hasCompactSupport
import Mathlib
import Definitions.Def_ChapterSchrodingerCutoffEsa
open BookProof.SchrodingerCutoff




open MeasureTheory Filter Complex

set_option maxHeartbeats 1000000 in
theorem solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {g g' : ℝ → E} (h : ∀ x, HasDerivAt g (g' x) x) (hc : Continuous g')
    (hs : HasCompactSupport g) : ∫ x, g' x = 0 := by

  obtain ⟨M, hMpos, hM⟩ := hs.exists_pos_le_norm
  have hvanish : ∀ x : ℝ, M < |x| → g' x = 0 := by
    intro x hx
    have hnb : g =ᶠ[nhds x] fun _ => (0 : E) := by
      filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hx] with y hy
      exact hM y (le_of_lt hy)
    exact (h x).unique ((hasDerivAt_const x (0 : E)).congr_of_eventuallyEq hnb)
  have hsub : ∫ x, g' x = ∫ x in Set.Ioc (-(M + 1)) (M + 1), g' x := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    refine hvanish x ?_
    simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hx
    rcases hx with hx | hx
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  rw [hsub, ← intervalIntegral.integral_of_le (by linarith)]
  rw [show (fun x => g' x) = deriv g from funext fun x => ((h x).deriv).symm]
  rw [intervalIntegral.integral_deriv_eq_sub (fun x _ => (h x).differentiableAt)
      (by rw [show deriv g = g' from funext fun x => (h x).deriv]
          exact hc.intervalIntegrable _ _)]
  rw [hM (M + 1) (by rw [Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith),
      hM (-(M + 1)) (by rw [Real.norm_eq_abs, abs_of_nonpos (by linarith)]; linarith)]
  simp
