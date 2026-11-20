-- Prove2me | solution 1 for DeletionCode.PaperProbability.total_discard_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:30:31.439825+00:00
-- url     : https://prove2.me/submissions/23f74926-4fbc-480a-9f4e-18c162751b23

import Definitions.Def_DeletionCode_NonseparatedFamily
import Definitions.Def_DeletionCode_ObstructionBound
import Definitions.Def_DeletionCode_PaperParameters
import Definitions.Def_DeletionCode_PaperProbability
import Theorems.Thm_DeletionCode_PaperProbability_labels_ge_two
import Theorems.Thm_DeletionCode_PaperProbability_exceptional_quarter_bound
import Theorems.Thm_DeletionCode_EditAlignment_Script_trans
import Theorems.Thm_DeletionCode_ObstructionBound_obstruction_measure_le
import Theorems.Thm_DeletionCode_PaperParameters_le_two_pow_of_L_lt
import Theorems.Thm_DeletionCode_PaperParameters_nine_le_L
import Theorems.Thm_DeletionCode_PaperParameters_threshold


set_option autoImplicit true
open DeletionCode DeletionCode.PaperProbability
open MeasureTheory Windows HeaderRecovery SignedSupport CircleUniform
open ExceptionalCountArithmetic ExceptionalProbability ObstructionProbability
open scoped ENNReal
namespace DeletionCode.PaperProbability
theorem _root_.solution {n : ℕ} (t Q : ℕ) (ht : 2 ≤ t) (x : Bits n)
    (hx : KUnique (padBits x) n (PaperParameters.k n))
    (hfit : PaperParameters.L n ≤ n) (hready : threshold t ≤ PaperParameters.L n)
    (hQ : 8 * ObstructionBound.scale t n (PaperParameters.k n) ≤ Q) :
    realWeights (Gram (PaperParameters.L n))
      (exceptionalEvent t (PaperParameters.k n) Q x ∪ obstructionEvent t (PaperParameters.k n) Q x) ≤
        ENNReal.ofReal (1 / 3 : ℝ) := by
  have hn : 1 ≤ n := by have := PaperParameters.nine_le_L n; omega
  have hL : 4 * t + 2 ≤ PaperParameters.L n := (le_max_left _ _).trans hready
  have hC : exceptionalConstant t ≤ PaperParameters.L n := (le_max_right _ _).trans hready
  calc
    _ ≤ realWeights (Gram (PaperParameters.L n)) (exceptionalEvent t (PaperParameters.k n) Q x) +
        realWeights (Gram (PaperParameters.L n)) (obstructionEvent t (PaperParameters.k n) Q x) :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal (1 / 4 : ℝ) + ENNReal.ofReal (1 / 12 : ℝ) :=
      add_le_add (exceptional_quarter_bound t Q x hx hfit hC hQ)
        (ObstructionBound.obstruction_measure_le t (PaperParameters.k n) Q ht x hx hn hL
          (PaperParameters.le_two_pow_of_L_lt n) hQ (labels_ge_two t n Q hn hQ))
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      norm_num
end DeletionCode.PaperProbability
