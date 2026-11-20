-- Prove2me | solution 1 for DeletionCode.RelationBlockSupport.partial_sum_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:12:56.444449+00:00
-- url     : https://prove2.me/submissions/464108a6-aa8e-4047-88b5-fc6e09d05b79

import Definitions.Def_DeletionCode_RelationSupport
import Definitions.Def_DeletionCode_RelationBlockSupport

set_option autoImplicit true
open DeletionCode DeletionCode.RelationBlockSupport
open SignedSupport RuleSetGraph GeneratingBlocks
open scoped BigOperators
namespace DeletionCode.RelationBlockSupport
theorem _root_.solution {I H : Type*} (G : I → H → ℚ)
    (hG : LinearIndependent ℚ G) (T : Finset I) (a : I → ℚ)
    (hactive : ∃ i ∈ T, a i ≠ 0) :
    ∃ g, (∑ i ∈ T, a i * G i g) ≠ 0 := by
  classical
  by_contra hnone
  push Not at hnone
  have hzero : (∑ i ∈ T, a i • G i) = 0 := by
    funext g
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      using hnone g
  obtain ⟨i, hi, hai⟩ := hactive
  exact hai ((linearIndependent_iff'.mp hG) T a hzero i hi)
end DeletionCode.RelationBlockSupport
