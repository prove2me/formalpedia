-- Prove2me | solution 1 for DerivativeChainPhaseLock.disk_phase_control
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T06:17:05.529388+00:00
-- url     : https://prove2.me/submissions/513808f6-5c21-418f-8f7f-e14b32b5d520

import Mathlib
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainFiniteHistory
end DerivativeChainFiniteHistory
namespace DerivativeChainPhaseLock
end DerivativeChainPhaseLock
namespace DerivativeChainPrefixLaws
end DerivativeChainPrefixLaws
namespace DerivativeChainPrivate
end DerivativeChainPrivate



set_option autoImplicit false
set_option maxHeartbeats 1500000
open DerivativeChainPhaseLock

theorem solution (Z : ℂ) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hZ : ‖Z-1‖ ≤ ε) :
    0 < Z.re ∧ |Z.arg| ≤ Real.arcsin ε := by
  have hre : 1-Z.re ≤ ε := by
    calc
      1-Z.re = (1-Z).re := by simp
      _ ≤ ‖1-Z‖ := Complex.re_le_norm _
      _ = ‖Z-1‖ := norm_sub_rev _ _
      _ ≤ ε := hZ
  have hx : 0 < Z.re := by linarith
  have hne : Z ≠ 0 := by intro h; rw [h] at hx; norm_num at hx
  have hr : 0 < ‖Z‖ := norm_pos_iff.mpr hne
  have hs : ‖Z‖^2=Z.re^2+Z.im^2 := by rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]; ring
  have he : ‖Z-1‖^2=(Z.re-1)^2+Z.im^2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply]
    ring
  have hds : (Z.re-1)^2+Z.im^2 ≤ ε^2 := by
    rw [← he]
    exact (sq_le_sq₀ (norm_nonneg _) hε).mpr hZ
  have hp := mul_le_mul_of_nonneg_right hds (sq_nonneg ‖Z‖)
  have hlink := congrArg (fun t : ℝ => ‖Z‖^2*t) hs
  have himsq : Z.im^2 ≤ ε^2*‖Z‖^2 := by
    nlinarith only [hp,hs,hlink,sq_nonneg (‖Z‖^2-Z.re)]
  have him : |Z.im| ≤ ε*‖Z‖ := by
    apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hε (norm_nonneg _))).mp
    simpa only [sq_abs,mul_pow] using himsq
  have hratio : |Z.im/‖Z‖| ≤ ε := by
    rw [abs_div,abs_of_pos hr]
    exact (div_le_iff₀ hr).mpr him
  refine ⟨hx,?_⟩
  rw [Complex.arg_of_re_nonneg hx.le]
  apply abs_le.mpr
  constructor
  · have h := Real.arcsin_le_arcsin (abs_le.mp hratio).1
    simpa only [Real.arcsin_neg] using h
  · exact Real.arcsin_le_arcsin (abs_le.mp hratio).2
