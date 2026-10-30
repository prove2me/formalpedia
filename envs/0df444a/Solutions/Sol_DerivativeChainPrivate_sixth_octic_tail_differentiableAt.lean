-- Prove2me | solution 1 for DerivativeChainPrivate.sixth_octic_tail_differentiableAt
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T01:26:17.113033+00:00
-- url     : https://prove2.me/submissions/831687f3-4014-41d6-9753-e780d8178b96

import Mathlib
import Definitions.Def_DerivativeChainPrivate_SixthOcticAlgebra
import Definitions.Def_DerivativeChainPrivate_SixthOcticTail
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPrivate_sixth_octic_denominator_bound
import Theorems.Thm_DerivativeChainPrivate_sixth_octic_radicand_im_nonzero
import Theorems.Thm_DerivativeChainPrivate_sixth_octic_real_positive
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
open Polynomial DerivativeChainPrivate MeasureTheory Set Filter
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped Topology BigOperators


set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace DerivativeChainPrivate





theorem sixth_octic_slit (u : ℂ) (hu : ‖u‖≤3/10) : sixthOcticRadicand u∈Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases hi : u.im=0
  · left
    have he : u=(u.re:ℂ) := by apply Complex.ext <;> simp [hi]
    rw [he]
    have hreal:=sixth_octic_real_positive u.re ((Complex.abs_re_le_norm u).trans hu)
    simpa [sixthOcticRadicand,←Complex.ofReal_pow] using hreal
  · exact Or.inr (sixth_octic_radicand_im_nonzero u hu hi)





theorem sixth_octic_pole_bound (u : ℂ) (hu : ‖u‖≤3/10) :
    1-(17/33:ℂ)*u≠0 ∧ ‖(1-(17/33:ℂ)*u)⁻¹‖≤6/5 := by
  have hn:=norm_sub_norm_le (1:ℂ) ((17/33:ℂ)*u)
  norm_num [norm_mul] at hn
  have hl : (5/6:ℝ)≤‖1-(17/33:ℂ)*u‖ := by linarith
  refine ⟨norm_pos_iff.mp (by linarith),?_⟩
  rw [norm_inv]
  have hi:=inv_anti₀ (by norm_num : (0:ℝ)<5/6) hl
  norm_num at hi
  exact hi
end DerivativeChainPrivate

theorem solution (w : ℂ) (hw : ‖w‖≤27/50) :
    DifferentiableAt ℂ sixthOcticTail w := by
  have hu : ‖w^2‖≤3/10 := by rw [norm_pow]; nlinarith [norm_nonneg w]
  have hh : DifferentiableAt ℂ (fun v : ℂ => sixthOcticRadicand (v^2)) w := by
    unfold sixthOcticRadicand
    fun_prop
  have hs : DifferentiableAt ℂ (fun v : ℂ => Complex.sqrt (sixthOcticRadicand (v^2))) w := by
    simpa only [Function.comp_def] using
      (Complex.differentiableAt_sqrt (sixth_octic_slit (w^2) hu)).comp w hh
  have hpoly : DifferentiableAt ℂ (fun v : ℂ => sixthOcticPoly (v^2)) w := by unfold sixthOcticPoly; fun_prop
  have ht : DifferentiableAt ℂ (fun v : ℂ => sixthOcticResidual (v^2)) w := by unfold sixthOcticResidual; fun_prop
  have hd:=(sixth_octic_denominator_bound (w^2) hu).1
  have hp:=(sixth_octic_pole_bound (w^2) hu).1
  unfold sixthOcticTail
  fun_prop
