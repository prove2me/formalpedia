-- Prove2me | solution 1 for DeletionCode.RandomHash.real_nonzero_test_probability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:23:49.613082+00:00
-- url     : https://prove2.me/submissions/81574758-f186-48f1-acba-05ca65a2e217

import Definitions.Def_DeletionCode_IntegerTorusMap
import Definitions.Def_DeletionCode_TorusHaar
import Definitions.Def_DeletionCode_CircleUniform
import Definitions.Def_DeletionCode_RandomHash
import Theorems.Thm_DeletionCode_RandomHash_rational_ne_zero
import Theorems.Thm_DeletionCode_RandomHash_real_simultaneous_test_probability
import Theorems.Thm_DeletionCode_IntegerTorusMap_jointHash_apply
attribute [local simp] DeletionCode.IntegerTorusMap.jointHash_apply



set_option autoImplicit true
open DeletionCode DeletionCode.RandomHash
open MeasureTheory ProbabilityTheory CircleHash IntegerTorusMap CircleUniform
open scoped BigOperators
variable {I J : Type*} [Fintype I] [Fintype J]
namespace DeletionCode.RandomHash
theorem _root_.solution (w : I → ℤ) (hw : w ≠ 0) (Q : ℕ) (hQ : 2 ≤ Q) :
    realWeights I {weights | ‖realWeightedHash weights w‖ < 1 / (Q : ℝ)} =
      ENNReal.ofReal (2 / (Q : ℝ)) := by
  have hi : LinearIndependent ℚ (fun _ : Fin 1 => fun i => (w i : ℚ)) :=
    LinearIndependent.of_subsingleton 0 (rational_ne_zero w hw)
  simpa only [Fin.forall_fin_one, Fintype.card_fin, pow_one] using
    real_simultaneous_test_probability (fun _ : Fin 1 => w) hi Q hQ
end DeletionCode.RandomHash
