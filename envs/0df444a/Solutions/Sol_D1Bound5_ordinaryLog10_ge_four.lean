-- Prove2me | solution 1 for D1Bound5.ordinaryLog10_ge_four
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:46:11.985525+00:00
-- url     : https://prove2.me/submissions/0a3a0f42-3a99-480f-b150-d1959a333f49

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_OrdinaryLog10_Definitions
import Theorems.Thm_D1Bound5_ordinaryLog10_mono
import Theorems.Thm_D1Bound5_ordinaryLog10_pow
import Theorems.Thm_D1Bound5_ordinaryLog10_ten

section
namespace D1Bound5



theorem _root_.solution {S : ℝ} (hS : 10000 ≤ S) :
    4 ≤ ordinaryLog10 S := by
  have h := ordinaryLog10_mono (by norm_num : (0 : ℝ) < 10^4)
    (show (10 : ℝ)^4 ≤ S by norm_num; exact hS)
  simpa only [ordinaryLog10_pow,ordinaryLog10_ten,mul_one,Nat.cast_ofNat] using h





end D1Bound5
end
