-- Prove2me | solution 1 for DerivativeChainPhaseLock.weighted_lipschitz_square_bound
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T06:45:54.566251+00:00
-- url     : https://prove2.me/submissions/83e9da90-d7fd-40a7-81bf-ada38e499dd2

import Mathlib
import Theorems.Thm_DerivativeChainContinuation_finite_weighted_variance
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
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
open DerivativeChainContinuation
namespace DerivativeChainPhaseLock
noncomputable section

theorem weighted_pairwise_variance {N : ℕ} (w : Fin N → ℝ) (a : Fin N → ℂ) (u : ℂ)
    (hs : ∑ i,w i=1) (hm : ∑ i,(w i:ℂ)*a i=u) :
    (∑ i,w i*(∑ j,w j*‖a i-a j‖^2))=2*(∑ i,w i*‖a i-u‖^2) := by
  have hv (i : Fin N) := finite_weighted_variance w a u (a i) hs hm
  have hrow (i : Fin N) : (∑ j,w j*‖a i-a j‖^2)=
      ‖a i-u‖^2+(∑ j,w j*‖a j-u‖^2) := by
    calc
      _ = ∑ j,w j*‖a j-a i‖^2 := by
        apply Finset.sum_congr rfl
        intro j _
        rw [norm_sub_rev (a i) (a j)]
      _ = _ := by simpa only [norm_sub_rev u (a i)] using hv i
  simp_rw [hrow,mul_add]
  rw [Finset.sum_add_distrib,← Finset.sum_mul,hs,one_mul]
  ring



end
end DerivativeChainPhaseLock



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
open DerivativeChainContinuation
open DerivativeChainPhaseLock




theorem solution {N : ℕ} (w : Fin N → ℝ) (a : Fin N → ℂ)
    (u : ℂ) (f : Fin N → ℝ) (hw : ∀ i,0 ≤ w i) (hs : ∑ i,w i=1)
    (hm : ∑ i,(w i:ℂ)*a i=u) (hf : ∀ i,0 ≤ f i)
    (hlip : ∀ i j,|f i-f j| ≤ ‖a i-a j‖) (T : ℝ) (hT : 0 ≤ T)
    (hmean : (∑ i,w i*f i) ≤ T) :
    (∑ i,w i*(f i)^2) ≤ T^2+(∑ i,w i*‖a i-u‖^2) := by
  let μ : ℝ := ∑ i,w i*f i
  have hmR : ∑ i,(w i:ℂ)*(f i:ℂ)=(μ:ℂ) := by exact_mod_cast (show (∑ i,w i*f i)=μ from rfl)
  have hvR := _root_.DerivativeChainContinuation.finite_weighted_variance w (fun i => (f i:ℂ)) (μ:ℂ) 0 hs hmR
  simp only [sub_zero,Complex.norm_real,Real.norm_eq_abs,sq_abs,
    ← Complex.ofReal_sub] at hvR
  have hpR := _root_.DerivativeChainPhaseLock.weighted_pairwise_variance w (fun i => (f i:ℂ)) (μ:ℂ) hs hmR
  simp only [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,sq_abs] at hpR
  have hpC := _root_.DerivativeChainPhaseLock.weighted_pairwise_variance w a u hs hm
  have hpair : (∑ i,w i*(∑ j,w j*(f i-f j)^2)) ≤
      ∑ i,w i*(∑ j,w j*‖a i-a j‖^2) := by
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left _ (hw i)
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left _ (hw j)
    exact (sq_abs (f i-f j)) ▸ (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2 (hlip i j)
  rw [hpR,hpC] at hpair
  have hμ : 0 ≤ μ := Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hf i))
  have hμT : μ^2 ≤ T^2 := (sq_le_sq₀ hμ hT).2 hmean
  linarith
