-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerBridge.binaryAngularFundamentalBox_eq_translate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/a20d5270-6d61-419a-8044-c3e505ffb78c

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.MatrixTorusBochnerBridge
open Set Function MeasureTheory Filter Matrix
open WeightedTorusHilbert EqualitySaturatingKillingPaths WeightedTorusDistributionBridge
open WeightedDolbeaultBochnerIdentity
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.MatrixTorusBochnerBridge
theorem _root_.solution
    {n : ℕ} (q : Fin n → Bool) :
    (fun t : Space n =>
      binaryAngularFundamentalBase q + t) ''
        angularFundamentalBox (0 : Space n) =
      angularFundamentalBox (binaryAngularFundamentalBase q) := by
  ext t
  constructor
  · rintro ⟨u, hu, rfl⟩
    intro i
    have hi : 0 < u i ∧ u i ≤ (1 : ℝ) := by
      simpa using hu i
    change
      binaryAngularFundamentalBase q i <
        binaryAngularFundamentalBase q i + u i ∧
      binaryAngularFundamentalBase q i + u i ≤
        binaryAngularFundamentalBase q i + 1
    constructor <;> linarith
  · intro ht
    refine ⟨t - binaryAngularFundamentalBase q, ?_, ?_⟩
    · intro i
      have hi := ht i
      change
        binaryAngularFundamentalBase q i < t i ∧
        t i ≤ binaryAngularFundamentalBase q i + 1 at hi
      have hp :
          0 < t i - binaryAngularFundamentalBase q i ∧
            t i - binaryAngularFundamentalBase q i ≤ (1 : ℝ) := by
        constructor <;> linarith
      simpa using hp
    · funext i
      change
        binaryAngularFundamentalBase q i +
          (t i - binaryAngularFundamentalBase q i) = t i
      ring
end Ehrhart.MatrixTorusBochnerBridge
