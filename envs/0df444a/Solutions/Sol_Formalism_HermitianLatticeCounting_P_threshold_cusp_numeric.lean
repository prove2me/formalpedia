-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.threshold_cusp_numeric
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:55:00.713623+00:00
-- url     : https://prove2.me/submissions/7e88facc-ed00-48ca-9d08-54939d7534ca

import Definitions.Def_Formalism_FlagUnipotentLattices_CuspidalityThreshold
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExtensionInterSubspace
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_NearFarVolumeBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_OperatorHilbertSchmidtNorm
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_CoefficientBoundLemmas_key


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory NumberField
open scoped ComplexOrder
open Formalism.NuclearRankWeightBounds.D (lead hs q0)
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : CuspidalityThreshold := by
  intro n q h hq hqn hh
  have hq' : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hqn' : 2 * (q:ℝ) ≤ n := by exact_mod_cast hqn
  have e : Real.sqrt (2 * (q : ℝ)) = Real.sqrt 2 * Real.sqrt q := Real.sqrt_mul (by norm_num) _
  rw [e]
  set r := Real.sqrt 2 with hr
  set s := Real.sqrt (q:ℝ) with hs'
  have r2 : r * r = 2 := Real.mul_self_sqrt (by norm_num)
  have s2 : s * s = q := Real.mul_self_sqrt (by linarith)
  have r0 : 0 < r := Real.sqrt_pos.mpr (by norm_num)
  have s1 : 1 ≤ s := by rw [hs']; exact Real.one_le_sqrt.mpr hq'
  have rU : r < 1.415 := by
    by_contra hc
    push Not at hc
    nlinarith
  have hns : 2 * s ≤ n := by nlinarith
  have hn0 : (0:ℝ) < n := by linarith
  rw [lt_div_iff₀ (by positivity)]
  have key : (2 * (n:ℝ) * (r * s) + 2 * (n:ℝ) ^ 2) * (r * s)
      = 2 * n * (r * r) * (s * s) + 2 * (n:ℝ) ^ 2 * r * s := by ring
  rw [key, r2]
  have a1 : 2 * (n:ℝ) * 2 * (s * s) ≤ 2 * (n:ℝ) ^ 2 * s := by
    have : (n:ℝ) * s * (2 * s) ≤ (n:ℝ) * s * n := by gcongr
    nlinarith
  have a2 : 2 * (n:ℝ) ^ 2 * r * s < 2.83 * ((n:ℝ) ^ 2 * s) := by
    have : 0 < (n:ℝ) ^ 2 * s := by positivity
    nlinarith
  have a3 : 0 < (n:ℝ) ^ 2 * s := by positivity
  nlinarith
end Formalism.HermitianLatticeCounting.P
