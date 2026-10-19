-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerBridge.integral_angularSmoothPartition_eq_angularHaar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/d5c11079-a6b2-45b5-a2f7-aee1be0beae8

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_integral_angularSmoothPartition_eq_fundamental
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_angularFundamental_integral_eq_haar

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
    {n : ℕ}
    {g : TorusCharacters.AngularTorus n → ℂ}
    (hg : Continuous g) :
    (∫ t : Space n,
      (angularSmoothPartition t : ℂ) *
        g (angularCoverProjection n t)
      ∂(volume : Measure (Space n))) =
      ∫ θ : TorusCharacters.AngularTorus n,
        g θ ∂(angularMeasure n) := by
  have hcont :
      Continuous (fun t : Space n =>
        g (angularCoverProjection n t)) :=
    hg.comp (continuous_angularCoverProjection n)
  have hperiod :
      ∀ (q : Fin n → Bool) (t : Space n),
        g (angularCoverProjection n
          (binaryAngularFundamentalBase q + t)) =
        g (angularCoverProjection n t) := by
    intro q t
    apply congrArg g
    let u : Fin n → ℤ :=
      fun i => if q i then (-1 : ℤ) else 0
    have heq :
        binaryAngularFundamentalBase q + t =
          fun i : Fin n => t i + (u i : ℝ) := by
      funext i
      simp only [Pi.add_apply,
        binaryAngularFundamentalBase, u]
      split <;> simp ; ring
    rw [heq, angularCoverProjection_integer_add]
  calc
    _ = ∫ t : Space n
      in angularFundamentalBox (0 : Space n),
      g (angularCoverProjection n t)
      ∂(volume : Measure (Space n)) :=
      integral_angularSmoothPartition_eq_fundamental hcont hperiod
    _ = _ := angularFundamental_integral_eq_haar hg
end Ehrhart.MatrixTorusBochnerBridge
