-- Prove2me | solution 1 for Bl.PowerApplication.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:24.9679+00:00
-- url     : https://prove2.me/submissions/a43af66b-b151-4ec8-9aff-8fbfa28f34bb

import Mathlib
import Definitions.Def_Lemmata_PowerApplication_PowApp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Polynomial Finset
namespace Bl.PowerApplication
variable {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
private theorem pow_app {T : Module.End ℂ Y} {z : ℂ} {f : Y} (hf : T f = z • f) (n : ℕ) :
    (T ^ n) f = z ^ n • f := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hf, smul_smul, pow_succ]
end Bl.PowerApplication
end

set_option autoImplicit false
open Polynomial Finset
open Bl Bl.PowerApplication
variable {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
namespace Bl.PowerApplication
theorem _root_.solution {T : Module.End ℂ Y} {z : ℂ} {f : Y} (hf : T f = z • f) (p : ℂ[X]) :
    aeval T p f = p.eval z • f := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, LinearMap.add_apply, hp, hq, eval_add, add_smul]
  | monomial n a =>
    rw [aeval_monomial, Module.End.mul_apply, pow_app hf, Module.algebraMap_end_apply,
      smul_smul, eval_monomial]
end Bl.PowerApplication
