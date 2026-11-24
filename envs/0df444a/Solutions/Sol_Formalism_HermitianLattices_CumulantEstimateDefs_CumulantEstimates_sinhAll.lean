-- Prove2me | solution 1 for Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.sinhAll
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:38.539629+00:00
-- url     : https://prove2.me/submissions/e8c6a648-cd4e-4711-8abd-e054fda94cb5

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_QuadraticFormLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HilbertSchmidtHalfBound
import Theorems.Thm_Formalism_HermitianLattices_CumulantEstimateDefs_CumulantEstimates_sinhMid

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.CumulantEstimateDefs Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
open Finset
open scoped Nat
namespace Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
theorem _root_.solution : Formalism.HermitianLattices.CumulantEstimateDefs.SinhBounds := by
  unfold Formalism.HermitianLattices.CumulantEstimateDefs.SinhBounds
  intro x hx
  have hs := Real.hasSum_sinh x
  have hlow : x ≤ Real.sinh x := by
    have h := le_hasSum hs 0 (fun j _ => by positivity)
    simpa using h
  have hc : HasSum (fun n : ℕ => x * (x ^ (2 * n) / ((2 * n)! : ℝ))) (x * Real.cosh x) :=
    (Real.hasSum_cosh x).mul_left x
  have h1 : Real.sinh x ≤ x * Real.cosh x := by
    refine hasSum_le (fun n => ?_) hs hc
    have hfac : ((2 * n)! : ℝ) ≤ ((2 * n + 1)! : ℝ) := by
      exact_mod_cast Nat.factorial_le (by omega)
    calc x ^ (2 * n + 1) / ((2 * n + 1)! : ℝ) = x * (x ^ (2 * n) / ((2 * n + 1)! : ℝ)) := by
          rw [pow_succ]
          ring
      _ ≤ x * (x ^ (2 * n) / ((2 * n)! : ℝ)) := by
          gcongr
  have h2 : Real.cosh x ≤ Real.exp x := by
    rw [Real.cosh_eq]
    have := Real.exp_le_exp.2 (show -x ≤ x by linarith)
    linarith
  exact ⟨hlow, sinhMid x hx, h1.trans (mul_le_mul_of_nonneg_left h2 hx.le)⟩
end Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
