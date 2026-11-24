-- Prove2me | solution 1 for GaussianPerimeter.measurable_facetAcceptanceProbability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:25:56.352885+00:00
-- url     : https://prove2.me/submissions/320af3ad-709d-4550-aa1f-b922aecc00a5

module
public import Definitions.Def_GaussianPerimeter_Geometry
public import Definitions.Def_GaussianPerimeter_Sphere
public import Definitions.Def_GaussianPerimeter_Averaging

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Function
open scoped ENNReal RealInnerProductSpace InnerProductSpace
open GaussianPerimeter
local notation "Euc" k => EuclideanSpace ℝ (Fin k)
local notation "UnitSphere" k => Metric.sphere (0 : Euc (k + 1)) 1
namespace GaussianPerimeter
theorem _root_.solution (k : ℕ) (ρ : ℝ) :
    Measurable (facetAcceptanceProbability k ρ) := by
  let e : Euc (k + 1) := EuclideanSpace.basisFun (Fin (k + 1)) ℝ 0
  let S := {p : ℝ × UnitSphere k | ⟪Real.sqrt (ρ ^ 2 + p.1 ^ 2) • e, p.2.val⟫_ℝ < ρ}
  have hS : MeasurableSet S := by
    apply measurableSet_lt _ measurable_const
    apply Continuous.measurable2 continuous_inner _ (measurable_subtype_coe.comp measurable_snd)
    have hm : Measurable (fun p : ℝ × UnitSphere k => Real.sqrt (ρ ^ 2 + p.1 ^ 2)) :=
      Real.continuous_sqrt.measurable.comp
        ((measurable_const (a := ρ ^ 2)).add (measurable_fst.pow_const 2))
    exact hm.smul (measurable_const (a := e))
  exact measurable_measure_prodMk_left (ν := uniformSphere (Euc (k + 1))) hS
end GaussianPerimeter
