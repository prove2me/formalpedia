-- Prove2me | solution 1 for Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.sinhMid
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:45.264806+00:00
-- url     : https://prove2.me/submissions/54e3b34f-fb89-482b-b5f6-7802ba614864

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_QuadraticFormLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HilbertSchmidtHalfBound
import Theorems.Thm_Formalism_HermitianLattices_CumulantEstimateDefs_CumulantEstimates_factIneq

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
theorem _root_.solution (x : ℝ) (hx : 0 < x) : Real.sinh x ≤ x * Real.exp (x ^ 2 / 6) := by
  have hs := Real.hasSum_sinh x
  have he : HasSum (fun n : ℕ => (x ^ 2 / 6) ^ n / (n ! : ℝ)) (Real.exp (x ^ 2 / 6)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp (x ^ 2 / 6)
  have hb : HasSum (fun n : ℕ => x * ((x ^ 2 / 6) ^ n / (n ! : ℝ))) (x * Real.exp (x ^ 2 / 6)) :=
    he.mul_left x
  refine hasSum_le (fun n => ?_) hs hb
  have hf : ((6 ^ n * n ! : ℕ) : ℝ) ≤ ((2 * n + 1)! : ℝ) := by exact_mod_cast factIneq n
  push_cast at hf
  have hn : (n ! : ℝ) ≠ 0 := by positivity
  have hpos : (0 : ℝ) < 6 ^ n * n ! := by positivity
  calc x ^ (2 * n + 1) / ((2 * n + 1)! : ℝ) ≤ x ^ (2 * n + 1) / (6 ^ n * n ! : ℝ) := by
        gcongr
    _ = x * ((x ^ 2 / 6) ^ n / (n ! : ℝ)) := by
        rw [div_pow]
        field_simp
        ring
end Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
