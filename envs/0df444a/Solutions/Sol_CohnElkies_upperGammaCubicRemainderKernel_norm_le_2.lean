-- Prove2me | solution 2 for CohnElkies.upperGammaCubicRemainderKernel_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:43:37.008784+00:00
-- url     : https://prove2.me/submissions/f1c1f6e8-e486-4d04-987f-f7ce4148d7bf

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

theorem h47c_iwd {x : ℝ} (hx : 0 < x) (k : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) x) :
    iteratedDerivWithin k CohnElkies.upperImaginaryExp (Set.Icc (0:ℝ) x) t =
      Complex.I ^ k * CohnElkies.upperImaginaryExp t := by
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hx)
    (h47_uie_contDiff.contDiffAt.of_le (by exact_mod_cast le_top)) ht, h47_uie_iter]

theorem h47c_cubic_pos {x : ℝ} (hx : 0 < x) :
    ‖Complex.exp (Complex.I * (x : ℂ)) - 1 - Complex.I * (x : ℂ) + ((x ^ 2 / 2 : ℝ) : ℂ)‖ ≤ x ^ 3 / 6 := by
  have hcd : ContDiffOn ℝ ((2 + 1 : ℕ) : WithTop ℕ∞) CohnElkies.upperImaginaryExp (Set.uIcc 0 x) :=
    (h47_uie_contDiff.of_le (by exact_mod_cast le_top)).contDiffOn
  have hT := taylor_integral_remainder hcd
  rw [Set.uIcc_of_le hx.le] at hT
  have htay : taylorWithinEval CohnElkies.upperImaginaryExp 2 (Set.Icc (0 : ℝ) x) 0 x =
      1 + Complex.I * (x : ℂ) - ((x ^ 2 / 2 : ℝ) : ℂ) := by
    have hm : (0:ℝ) ∈ Set.Icc (0:ℝ) x := ⟨le_rfl, hx.le⟩
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, h47c_iwd hx _ hm]
    simp [CohnElkies.upperImaginaryExp]
    ring_nf
  rw [htay] at hT
  have hL : Complex.exp (Complex.I * (x : ℂ)) - 1 - Complex.I * (x : ℂ) + ((x ^ 2 / 2 : ℝ) : ℂ) =
      CohnElkies.upperImaginaryExp x - (1 + Complex.I * (x : ℂ) - ((x ^ 2 / 2 : ℝ) : ℂ)) := by
    unfold CohnElkies.upperImaginaryExp; ring
  rw [hL, hT]
  calc ‖∫ t in (0 : ℝ)..x, ((x - t) ^ 2 / (Nat.factorial 2 : ℝ)) •
          iteratedDerivWithin (2 + 1) CohnElkies.upperImaginaryExp (Set.Icc 0 x) t‖
      ≤ ∫ t in (0 : ℝ)..x, (x - t) ^ 2 / 2 := by
        apply intervalIntegral.norm_integral_le_of_norm_le hx.le
        · refine Filter.Eventually.of_forall fun t ht => ?_
          rw [norm_smul, h47c_iwd hx _ ⟨ht.1.le, ht.2⟩, norm_mul, norm_pow, Complex.norm_I, one_pow,
            one_mul, h47_uie_norm, mul_one, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          norm_num
        · apply Continuous.intervalIntegrable; fun_prop
    _ = x ^ 3 / 6 := by
        rw [intervalIntegral.integral_comp_sub_left (fun t => t ^ 2 / 2) x]
        simp only [sub_self, sub_zero]
        rw [intervalIntegral.integral_div, integral_pow]
        ring

theorem h47c_cubic (x : ℝ) :
    ‖Complex.exp (Complex.I * (x : ℂ)) - 1 - Complex.I * (x : ℂ) + ((x ^ 2 / 2 : ℝ) : ℂ)‖ ≤ |x| ^ 3 / 6 := by
  rcases lt_trichotomy x 0 with h | h | h
  · have := h47c_cubic_pos (neg_pos.mpr h)
    rw [abs_of_neg h]
    rw [← Complex.norm_conj] at this
    convert this using 2
    simp only [map_add, map_sub, map_mul, map_one, Complex.conj_I, Complex.conj_ofReal, ← Complex.exp_conj]
    push_cast
    ring_nf
  · subst h; simp
  · rw [abs_of_pos h]; exact h47c_cubic_pos h

theorem solution
    {ℓ η a : ℝ} (hℓ : 0 < ℓ) (ha : 0 < a)
    (T : ℝ) :
    ‖upperGammaCubicRemainderKernel ℓ η T a‖ ≤
      (|T| ^ 3 / 6) *
        (a ^ 3 * upperGammaMeasureDensity ℓ η a) := by
  unfold upperGammaCubicRemainderKernel upperImaginaryExp
  have hd : 0 ≤ upperGammaMeasureDensity ℓ η a := by
    unfold upperGammaMeasureDensity
    apply div_nonneg (Real.exp_pos _).le
    apply mul_nonneg ha.le
    have : Real.exp (-(2 * a / ℓ)) < 1 := Real.exp_lt_one_iff.mpr (by have := div_pos (mul_pos two_pos ha) hℓ; linarith)
    linarith
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd]
  have := h47c_cubic (a * T)
  calc _ ≤ |a * T| ^ 3 / 6 * upperGammaMeasureDensity ℓ η a := by gcongr
    _ = _ := by rw [abs_mul, abs_of_pos ha]; ring

