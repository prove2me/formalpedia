-- Prove2me | solution 1 for DeletionCode.CircleHash.realWeightedHash_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:10.818746+00:00
-- url     : https://prove2.me/submissions/ee48b6a9-a194-46c4-a9f6-a5196fe7535e

import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Algebra.Order.Floor.Ring
import Definitions.Def_DeletionCode_CircleHash

set_option autoImplicit true
open DeletionCode DeletionCode.CircleHash
open scoped BigOperators
namespace DeletionCode.CircleHash
theorem _root_.solution {I : Type*} [Fintype I]
    (weights : I → ℝ) (p : I → ℤ) :
    realWeightedHash weights p = ((∑ g, weights g * (p g : ℝ) : ℝ) : UnitAddCircle) := by
  change (∑ g, p g • (weights g : UnitAddCircle)) =
    ((∑ g, weights g * (p g : ℝ) : ℝ) : UnitAddCircle)
  calc
    (∑ g, p g • (weights g : UnitAddCircle)) =
        ∑ g, ((weights g * (p g : ℝ) : ℝ) : UnitAddCircle) := by
      apply Finset.sum_congr rfl
      intro g hg
      simpa only [zsmul_eq_mul, mul_comm] using
        (AddCircle.coe_zsmul (p := (1 : ℝ)) (n := p g) (x := weights g)).symm
    _ = ((∑ g, weights g * (p g : ℝ) : ℝ) : UnitAddCircle) :=
      (map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)))
        (fun g => weights g * (p g : ℝ)) Finset.univ).symm
end DeletionCode.CircleHash
