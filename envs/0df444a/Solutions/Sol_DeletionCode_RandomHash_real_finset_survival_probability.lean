-- Prove2me | solution 1 for DeletionCode.RandomHash.real_finset_survival_probability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:24:36.418786+00:00
-- url     : https://prove2.me/submissions/9ed565d3-ed11-458a-baac-68a6742b51fe

import Definitions.Def_DeletionCode_IntegerTorusMap
import Definitions.Def_DeletionCode_TorusHaar
import Definitions.Def_DeletionCode_CircleUniform
import Definitions.Def_DeletionCode_RandomHash
import Theorems.Thm_DeletionCode_RandomHash_real_rules_survival_probability
import Theorems.Thm_DeletionCode_IntegerTorusMap_jointHash_apply
attribute [local simp] DeletionCode.IntegerTorusMap.jointHash_apply



set_option autoImplicit true
open DeletionCode DeletionCode.RandomHash
open MeasureTheory ProbabilityTheory CircleHash IntegerTorusMap CircleUniform
open scoped BigOperators
variable {I J : Type*} [Fintype I] [Fintype J]
namespace DeletionCode.RandomHash
theorem _root_.solution (S : Finset (I → ℤ))
    (h : LinearIndependent ℚ (fun w : S => fun i => (w.val i : ℚ)))
    (K₀ : Set (I → ℤ)) (hS : ∀ w ∈ S, w ∈ K₀) (Q : ℕ) (hQ : 2 ≤ Q) :
    realWeights I {weights | ∀ w ∈ S, w ∈ surviving (realWeightedHash weights) Q K₀} =
      ENNReal.ofReal (2 / (Q : ℝ)) ^ S.card := by
  have ht := real_rules_survival_probability (fun w : S => w.val) h K₀
    (fun w => hS w.val w.property) Q hQ
  simpa only [Subtype.forall, Fintype.card_coe] using ht
end DeletionCode.RandomHash
