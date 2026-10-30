-- Prove2me | solution 1 for DerivativeChainPrivate.sixth_septic_tail_differentiableAt
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T01:05:22.737109+00:00
-- url     : https://prove2.me/submissions/6af1d9a0-31e6-4335-8820-735311c275d0

import Mathlib
import Definitions.Def_DerivativeChainPrivate_SixthSepticAlgebra
import Definitions.Def_DerivativeChainPrivate_SixthSepticTail
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPrivate_sixth_septic_denominator_bound
import Theorems.Thm_DerivativeChainPrivate_sixth_septic_radicand_positive
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
set_option maxHeartbeats 4000000
namespace DerivativeChainPrivate



theorem sixth_septic_slit (u : ℂ) (hu : ‖u‖≤3/8) :
    sixthSepticRadicand u∈Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl (sixth_septic_radicand_positive u hu))


end DerivativeChainPrivate

theorem solution (w : ℂ) (hw : ‖w‖≤3/5) :
    DifferentiableAt ℂ sixthSepticTail w := by
  have hu : ‖w^2‖≤3/8 := by rw [norm_pow]; nlinarith [norm_nonneg w]
  have hh : DifferentiableAt ℂ (fun v : ℂ => sixthSepticRadicand (v^2)) w := by
    unfold sixthSepticRadicand
    fun_prop
  have hs : DifferentiableAt ℂ (fun v : ℂ => Complex.sqrt (sixthSepticRadicand (v^2))) w := by
    simpa only [Function.comp_def] using
      (Complex.differentiableAt_sqrt (sixth_septic_slit (w^2) hu)).comp w hh
  have hp : DifferentiableAt ℂ (fun v : ℂ => sixthSepticPoly (v^2)) w := by
    unfold sixthSepticPoly
    fun_prop
  have ht : DifferentiableAt ℂ (fun v : ℂ => sixthSepticResidual (v^2)) w := by
    unfold sixthSepticResidual
    fun_prop
  have hd:=(sixth_septic_denominator_bound (w^2) hu).1
  unfold sixthSepticTail
  fun_prop
