-- Prove2me | solution 2 for CohnElkies.upperGammaEuler_log_norm_ratio
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:09:25.987777+00:00
-- url     : https://prove2.me/submissions/ca35188f-63bf-4323-99e6-a1c821a13d7a

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
theorem h47_log_ratio {A P1 P2 : ℝ} (hA : 0 < A) (h1 : 0 < P1) (h2 : 0 < P2) :
    Real.log ((A / P1) / (A / P2)) = Real.log P2 - Real.log P1 := by
  rw [div_div_div_cancel_left' _ _ hA.ne', Real.log_div h2.ne' h1.ne']

theorem solution
    {m : ℝ} (hm : 0 < m) (b : ℝ)
    {n : ℕ} (hn : 0 < n) :
    Real.log
      (‖Complex.GammaSeq
          ((m : ℂ) + Complex.I * (b : ℂ)) n‖ /
        ‖Complex.GammaSeq (m : ℂ) n‖) =
      -(∑ k ∈ Finset.range (n + 1),
        Real.log
          (‖(m : ℂ) + Complex.I * (b : ℂ) + (k : ℂ)‖ /
            (m + (k : ℝ)))) := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hprodpos : ∀ j ∈ Finset.range (n+1), 0 < ‖(m:ℂ) + Complex.I * (b:ℂ) + (j:ℂ)‖ := by
    intro j _
    refine norm_pos_iff.mpr (fun h => ?_)
    have h' := congrArg Complex.re h
    simp at h'
    have : (0:ℝ) ≤ j := j.cast_nonneg
    linarith
  have hmj : ∀ j : ℕ, 0 < m + (j:ℝ) := fun j => by positivity
  have hcp : ∀ s : ℂ, s.re = m → ‖(n:ℂ) ^ s‖ = (n:ℝ) ^ m := fun s hs => by
    rw [show (n:ℂ) = ((n:ℝ):ℂ) by norm_cast, Complex.norm_cpow_eq_rpow_re_of_pos hn', hs]
  have h1 : ‖Complex.GammaSeq ((m : ℂ) + Complex.I * (b : ℂ)) n‖ =
      (n:ℝ) ^ m * n.factorial / ∏ j ∈ Finset.range (n+1), ‖(m:ℂ) + Complex.I * (b:ℂ) + (j:ℂ)‖ := by
    unfold Complex.GammaSeq
    rw [norm_div, norm_mul, norm_prod, hcp _ (by simp), Complex.norm_natCast]
  have h2 : ‖Complex.GammaSeq (m : ℂ) n‖ =
      (n:ℝ) ^ m * n.factorial / ∏ j ∈ Finset.range (n+1), (m + (j:ℝ)) := by
    unfold Complex.GammaSeq
    rw [norm_div, norm_mul, norm_prod, hcp _ (by simp), Complex.norm_natCast]
    congr 1
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [show (m:ℂ) + (j:ℂ) = ((m + j : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (hmj j).le]
  have hA : 0 < (n:ℝ) ^ m * n.factorial := by positivity
  have hP1 := Finset.prod_pos hprodpos
  have hP2 : 0 < ∏ j ∈ Finset.range (n+1), (m + (j:ℝ)) := Finset.prod_pos (fun j _ => hmj j)
  rw [h1, h2, h47_log_ratio hA hP1 hP2, Real.log_prod (fun j _ => (hmj j).ne'),
    Real.log_prod (fun j hj => (hprodpos j hj).ne')]
  have hs : ∑ j ∈ Finset.range (n+1), Real.log (‖(m:ℂ) + Complex.I * (b:ℂ) + (j:ℂ)‖ / (m + (j:ℝ))) =
      ∑ j ∈ Finset.range (n+1), (Real.log ‖(m:ℂ) + Complex.I * (b:ℂ) + (j:ℂ)‖ - Real.log (m + (j:ℝ))) :=
    Finset.sum_congr rfl (fun j hj => Real.log_div (hprodpos j hj).ne' (hmj j).ne')
  rw [hs, Finset.sum_sub_distrib]
  ring

