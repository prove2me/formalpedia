-- Prove2me | solution 1 for DeletionCode.RandomHash.nonzero_test_probability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:22:49.785052+00:00
-- url     : https://prove2.me/submissions/186b7575-58cf-4069-bc9a-299c4a1c88d7

import Definitions.Def_DeletionCode_IntegerTorusMap
import Definitions.Def_DeletionCode_TorusHaar
import Definitions.Def_DeletionCode_CircleUniform
import Definitions.Def_DeletionCode_RandomHash
import Theorems.Thm_DeletionCode_RandomHash_simultaneous_test_probability
import Theorems.Thm_DeletionCode_RandomHash_rational_ne_zero
import Theorems.Thm_DeletionCode_IntegerTorusMap_jointHash_apply
attribute [local simp] DeletionCode.IntegerTorusMap.jointHash_apply



set_option autoImplicit true
open DeletionCode DeletionCode.RandomHash
open MeasureTheory ProbabilityTheory CircleHash IntegerTorusMap CircleUniform
open scoped BigOperators
variable {I J : Type*} [Fintype I] [Fintype J]
namespace DeletionCode.RandomHash
theorem _root_.solution (w : I → ℤ) (hw : w ≠ 0) (Q : ℕ) (hQ : 2 ≤ Q) :
    volume {weights : I → UnitAddCircle | ‖weightedHash weights w‖ < 1 / (Q : ℝ)} =
      ENNReal.ofReal (2 / (Q : ℝ)) := by
  have hi : LinearIndependent ℚ (fun _ : Fin 1 => fun i => (w i : ℚ)) :=
    LinearIndependent.of_subsingleton 0 (rational_ne_zero w hw)
  simpa only [Fin.forall_fin_one, Fintype.card_fin, pow_one] using
    simultaneous_test_probability (fun _ : Fin 1 => w) hi Q hQ
end DeletionCode.RandomHash
