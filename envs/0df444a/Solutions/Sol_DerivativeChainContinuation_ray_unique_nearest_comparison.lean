-- Prove2me | solution 1 for DerivativeChainContinuation.ray_unique_nearest_comparison
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T23:44:47.620082+00:00
-- url     : https://prove2.me/submissions/24a383a6-4063-463d-804f-121fc12dd33a

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators


set_option autoImplicit false
namespace DerivativeChainContinuation

theorem ray_geodesic_norm (w : ℂ) (t : ℝ) (ht : 1≤t) :
    ‖(t : ℂ)*w-w‖=‖(t : ℂ)*w‖-‖w‖ := by
  have hform : (t : ℂ)*w-w=((t-1 : ℝ) : ℂ)*w := by push_cast; ring
  rw [hform,norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,
    Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0≤t-1),
    abs_of_nonneg (by linarith : 0≤t)]
  ring







end DerivativeChainContinuation

theorem solution (w u : ℂ) (t : ℝ) (ht : 1≤t) (hw : w≠0)
    (hbound : ‖u‖≤‖(t : ℂ)*w‖)
    (hgap : ‖u‖<‖(t : ℂ)*w‖ → ‖(t : ℂ)*w‖+‖u‖<2*‖w‖) :
    ‖(t : ℂ)*w-w‖≤‖u-w‖ ∧
      (‖u-w‖≤‖(t : ℂ)*w-w‖ → u=(t : ℂ)*w) := by
  have hgeo := ray_geodesic_norm w t ht
  have htri : ‖u‖-‖w‖≤‖u-w‖ := norm_sub_norm_le u w
  by_cases hlt : ‖u‖<‖(t : ℂ)*w‖
  · have hg := hgap hlt
    have hlo : ‖w‖-‖u‖≤‖u-w‖ := by simpa only [norm_sub_rev] using norm_sub_norm_le w u
    have hstrict : ‖(t : ℂ)*w-w‖<‖u-w‖ := by linarith
    exact ⟨hstrict.le,fun hnear => False.elim ((not_lt_of_ge hnear) hstrict)⟩
  · have heq : ‖u‖=‖(t : ℂ)*w‖ := le_antisymm hbound (le_of_not_gt hlt)
    refine ⟨by linarith,?_⟩
    intro hnear
    have hdist : ‖u-w‖=‖(t : ℂ)*w-w‖ := by linarith
    have hadd : ‖(u-w)+w‖=‖u-w‖+‖w‖ := by rw [sub_add_cancel]; linarith
    have hcol := norm_add_eq_iff_real.mp hadd
    have hn : ‖(t : ℂ)*w‖=t*‖w‖ := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0≤t)]
    have hdist' : ‖u-w‖=(t-1)*‖w‖ := by linarith
    rw [hdist'] at hcol
    simp only [Complex.real_smul] at hcol
    have hnorm : (‖w‖ : ℂ)≠0 := by exact_mod_cast (norm_ne_zero_iff.mpr hw)
    have hmul : (‖w‖ : ℂ)*u=(‖w‖ : ℂ)*((t : ℂ)*w) := by
      push_cast at hcol
      linear_combination hcol
    exact mul_left_cancel₀ hnorm hmul
