-- Prove2me | solution 1 for DerivativeChainPhaseLock.large_gain_rms_budget
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T06:47:26.28999+00:00
-- url     : https://prove2.me/submissions/e026fbf0-e0de-4335-a34e-ef82946dd903

import Mathlib
import Theorems.Thm_DerivativeChainPhaseLock_large_gain_sqrt_bound
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
set_option maxHeartbeats 1000000
namespace DerivativeChainPhaseLock



theorem linear_gain_of_ratio (K v D : ℝ) (hK : 0 < K) (hv : 0 ≤ v) (hD : 0 < D)
    (hgain : Real.sqrt (v/D) ≤ (K-1)/(K+1)) :
    (K+1)*Real.sqrt v ≤ (K-1)*Real.sqrt D := by
  rw [Real.sqrt_div hv] at hgain
  have hcross := (div_le_div_iff₀ (Real.sqrt_pos.mpr hD) (by linarith : 0 < K+1)).mp hgain
  nlinarith only [hcross]

end DerivativeChainPhaseLock



set_option autoImplicit false
open DerivativeChainPhaseLock

theorem solution (K A2 v D B2 : ℝ) (hK : 0 < K) (hv : 0 ≤ v)
    (hvd : v ≤ D) (hB : 0 ≤ B2) (hchild : A2 ≤ K*v)
    (hrms : Real.sqrt B2 ≤ Real.sqrt A2+Real.sqrt (D-v))
    (hgain : D=0 ∨ Real.sqrt (v/D) ≤ (K-1)/(K+1)) : B2 ≤ K*D := by
  have hlinear : (K+1)*Real.sqrt v ≤ (K-1)*Real.sqrt D := by
    by_cases hD : 0 < D
    · apply _root_.DerivativeChainPhaseLock.linear_gain_of_ratio K v D hK hv hD
      rcases hgain with hz | hg
      · exfalso
        linarith
      · exact hg
    · have hzD : D=0 := le_antisymm (le_of_not_gt hD) (hv.trans hvd)
      have hzv : v=0 := by linarith
      simp only [hzD,hzv,Real.sqrt_zero,mul_zero,le_refl]
  have hsqrt : Real.sqrt B2 ≤ Real.sqrt (K*D) := by
    calc
      Real.sqrt B2 ≤ Real.sqrt A2+Real.sqrt (D-v) := hrms
      _ ≤ Real.sqrt (K*v)+Real.sqrt (D-v) :=
        add_le_add (Real.sqrt_le_sqrt hchild) (le_refl _)
      _ ≤ Real.sqrt (K*D) := _root_.DerivativeChainPhaseLock.large_gain_sqrt_bound K v D hK.le hv hvd hlinear
  have hsquare := (sq_le_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).mpr hsqrt
  simpa only [Real.sq_sqrt hB,Real.sq_sqrt (mul_nonneg hK.le (hv.trans hvd))] using hsquare
