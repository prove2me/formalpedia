-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.probability_nonzero_index
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:40.829795+00:00
-- url     : https://prove2.me/submissions/b05f7b73-cbda-4fbc-8a12-420c075c04f7

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : ProbINonzero := by
  intro c hc
  refine ⟨c / 2, by positivity, ⌈Real.exp (2 / c)⌉₊, ?_⟩
  intro n q J f hn hq hJ hf
  have hn1 : Real.exp (2 / c) ≤ n := Nat.ceil_le.mp hn
  have hn0 : (0:ℝ) < n := lt_of_lt_of_le (Real.exp_pos _) hn1
  have hlog : 2 / c ≤ Real.log n := (Real.le_log_iff_exp_le hn0).mpr hn1
  have hlog' : 2 ≤ c * Real.log n := by
    rw [div_le_iff₀ hc] at hlog; linarith
  have hqn1 : (q:ℝ) ≤ n := by
    have : q ≤ n := le_trans (Nat.le_self_pow (by norm_num) q) hq
    exact_mod_cast this
  have hJ' : (1:ℝ) ≤ J := by exact_mod_cast hJ
  have hf' : (1:ℝ) ≤ f := by exact_mod_cast hf
  have e2 : (2:ℝ) ^ q = Real.exp (q * Real.log 2) := by
    rw [mul_comm, ← Real.rpow_def_of_pos (by norm_num), Real.rpow_natCast]
  rw [e2, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hl2 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9; linarith
  have hl20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hq0 : (0:ℝ) ≤ q := Nat.cast_nonneg _
  have a1 : (q:ℝ) * Real.log 2 ≤ n := by nlinarith
  have hx : 0 ≤ c * Real.log n := by linarith
  have a2 : c * Real.log n * (n * f) ≤ c * Real.log n * (J * (n * f)) := by
    apply mul_le_mul_of_nonneg_left _ hx
    have : 0 ≤ (n:ℝ) * f := by positivity
    nlinarith
  have a3 : 2 * ((n:ℝ) * 1) ≤ c * Real.log n * (n * f) := by
    apply mul_le_mul hlog' _ (by positivity) hx
    gcongr
  nlinarith
end Formalism.HermitianLatticeCounting.P
