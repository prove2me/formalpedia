-- Prove2me | solution 1 for DerivativeChainContinuation.affine_greedy_iff
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T21:08:10.790785+00:00
-- url     : https://prove2.me/submissions/eadaa84b-18a6-4b08-9586-abea76f11097

import Mathlib
import Definitions.Def_DerivativeChainContinuation_GreedyActual
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_affine_complex_row_root_iff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators





theorem affine_complex_distance (o c z w : ℂ) :
    ‖(o+c*z)-(o+c*w)‖=‖c‖*‖z-w‖ := by
  rw [show (o+c*z)-(o+c*w)=c*(z-w) by ring,norm_mul]

theorem affine_inverse_value (o c w : ℂ) (hc : c≠0) : o+c*((w-o)/c)=w := by
  field_simp
  ring


















end DerivativeChainContinuation

theorem solution {n : ℕ} (a z : Fin (n+1) → ℂ)
    (o c : ℂ) (hc : c≠0) :
    IsGreedyChain (fun i => o+c*a i) (fun i => o+c*z i) ↔ IsGreedyChain a z := by
  have hcn : 0<‖c‖ := norm_pos_iff.mpr hc
  constructor
  · rintro ⟨hz,hnear⟩
    refine ⟨?_,?_⟩
    · intro i
      exact (affine_complex_row_root_iff a o c hc (i.val+1) (z i)).mp (hz i)
    · intro i w hw
      have hroot := (affine_complex_row_root_iff a o c hc (i.val+2) w).mpr hw
      have h := hnear i (o+c*w) hroot
      simp only [affine_complex_distance] at h
      exact (mul_le_mul_iff_right₀ hcn).mp h
  · rintro ⟨hz,hnear⟩
    refine ⟨?_,?_⟩
    · intro i
      exact (affine_complex_row_root_iff a o c hc (i.val+1) (z i)).mpr (hz i)
    · intro i w hw
      let v := (w-o)/c
      have hwfun : o+c*v=w := affine_inverse_value o c w hc
      have hvroot := (affine_complex_row_root_iff a o c hc (i.val+2) v).mp (by rwa [hwfun])
      have h := mul_le_mul_of_nonneg_left (hnear i v hvroot) hcn.le
      rw [←affine_complex_distance o c _ _,←affine_complex_distance o c _ _,hwfun] at h
      exact h
