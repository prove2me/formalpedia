-- Prove2me | solution 1 for Deduction.LFunctionConjugation.hurwitz_conj_of_re
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:37:18.092489+00:00
-- url     : https://prove2.me/submissions/9e17b68d-fd0f-4238-a5ce-b3434df28ed7

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_LFunctionConj
import Theorems.Thm_Deduction_LFunctionConjugation_ofReal_cpow_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Deduction
open Deduction.LFunctionConjugation
open HurwitzZeta
namespace Deduction.LFunctionConjugation
theorem _root_.solution {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) {s : ℂ} (hs : 1 < s.re) :
    hurwitzZeta a ((starRingEnd ℂ) s) = (starRingEnd ℂ) (hurwitzZeta a s) := by
  have hs' : 1 < ((starRingEnd ℂ) s).re := by rwa [Complex.conj_re]
  rw [← (hasSum_hurwitzZeta_of_one_lt_re ha hs').tsum_eq,
    ← (hasSum_hurwitzZeta_of_one_lt_re ha hs).tsum_eq, Complex.conj_tsum]
  refine tsum_congr fun n => ?_
  have hn : (0 : ℝ) ≤ (n : ℝ) + a := add_nonneg (Nat.cast_nonneg n) ha.1
  have hc : ((n : ℂ) + (a : ℂ)) = (((n : ℝ) + a : ℝ) : ℂ) := by push_cast; rfl
  rw [map_div₀, map_one, hc, ofReal_cpow_conj hn]
end Deduction.LFunctionConjugation
