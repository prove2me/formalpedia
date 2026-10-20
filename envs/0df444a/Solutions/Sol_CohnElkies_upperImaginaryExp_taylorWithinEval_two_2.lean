-- Prove2me | solution 2 for CohnElkies.upperImaginaryExp_taylorWithinEval_two
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:37:51.036847+00:00
-- url     : https://prove2.me/submissions/94c87656-6ed5-4cf4-9879-309a0e348249

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set intervalIntegral
open scoped Topology
theorem h47_uie_hasDerivAt (y : ℝ) :
    HasDerivAt CohnElkies.upperImaginaryExp (Complex.I * CohnElkies.upperImaginaryExp y) y := by
  have h1 : HasDerivAt (fun t : ℝ => Complex.I * (t : ℂ)) (Complex.I * 1) y :=
    (hasDerivAt_id (y : ℂ)).comp_ofReal.const_mul Complex.I
  have := h1.cexp
  unfold CohnElkies.upperImaginaryExp
  convert this using 1
  ring
theorem h47_uie_iter (m : ℕ) : iteratedDeriv m CohnElkies.upperImaginaryExp =
    fun y => Complex.I ^ m * CohnElkies.upperImaginaryExp y := by
  have hD : deriv CohnElkies.upperImaginaryExp = fun y => Complex.I * CohnElkies.upperImaginaryExp y :=
    funext fun y => (h47_uie_hasDerivAt y).deriv
  induction m with
  | zero => funext y; simp
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext y
    rw [deriv_const_mul _ (h47_uie_hasDerivAt y).differentiableAt, hD]
    ring
theorem h47_uie_norm (y : ℝ) : ‖CohnElkies.upperImaginaryExp y‖ = 1 := by
  unfold CohnElkies.upperImaginaryExp
  rw [Complex.norm_exp]
  simp
theorem h47_uie_contDiff : ContDiff ℝ ⊤ CohnElkies.upperImaginaryExp := by
  unfold CohnElkies.upperImaginaryExp
  exact Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)

theorem solution
    {x : ℝ} (hx : 0 < x) :
    taylorWithinEval upperImaginaryExp 2
      (Icc (0 : ℝ) x) 0 x =
        1 + Complex.I * (x : ℂ) -
          ((x ^ 2 / 2 : ℝ) : ℂ) := by
  have hU : UniqueDiffOn ℝ (Icc (0:ℝ) x) := uniqueDiffOn_Icc hx
  have hm : (0:ℝ) ∈ Icc (0:ℝ) x := ⟨le_rfl, hx.le⟩
  have hk : ∀ k : ℕ, iteratedDerivWithin k upperImaginaryExp (Icc (0:ℝ) x) 0 = Complex.I ^ k := by
    intro k
    rw [iteratedDerivWithin_eq_iteratedDeriv hU (h47_uie_contDiff.contDiffAt.of_le (by exact_mod_cast le_top)) hm, h47_uie_iter]
    simp [upperImaginaryExp]
  rw [taylor_within_apply]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hk]
  simp
  push_cast
  ring_nf

