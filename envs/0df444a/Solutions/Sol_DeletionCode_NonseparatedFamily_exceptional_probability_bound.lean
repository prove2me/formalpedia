-- Prove2me | solution 1 for DeletionCode.NonseparatedFamily.exceptional_probability_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:17:37.986491+00:00
-- url     : https://prove2.me/submissions/393676e4-6914-4ffb-8d1a-0ca12999973f

import Definitions.Def_DeletionCode_ExceptionalPartnerCount
import Definitions.Def_DeletionCode_NonseparatedFamily
import Theorems.Thm_DeletionCode_NonseparatedFamily_exceptional_measure_le

set_option autoImplicit true
open DeletionCode DeletionCode.NonseparatedFamily
open MeasureTheory Windows HeaderRecovery SignedSupport CircleHash CircleUniform ConflictGraphWitness
open ExceptionalProbability ExceptionalPartnerCount ExceptionalCountArithmetic
namespace DeletionCode.NonseparatedFamily
theorem _root_.solution {n : ℕ} (t k Q : ℕ) (x : Bits n)
    (hx : KUnique (padBits x) n k) (hn : windowLength k ≤ n) (hQ : 2 ≤ Q) :
    (realWeights (Gram (windowLength k)) (exceptionalEvent t k Q x)).toReal ≤
      2 * (exceptionalConstant t : ℝ) * (n : ℝ) ^ (2 * t - 1) * (windowLength k : ℝ) / Q := by
  have h := exceptional_measure_le t k Q x hx hn hQ
  have hfinite :
      ((exceptionalConstant t * windowLength k * n ^ (2 * t - 1) : ℕ) : ENNReal) *
        ENNReal.ofReal (2 / (Q : ℝ)) ≠ ⊤ := by finiteness
  have hr := ENNReal.toReal_mono hfinite h
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (div_nonneg (by norm_num) (Nat.cast_nonneg Q))] at hr
  convert hr using 1
  push_cast
  ring
end DeletionCode.NonseparatedFamily
