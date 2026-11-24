-- Prove2me | solution 1 for GaussianPerimeter.facetAcceptanceProbability_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:25:56.821797+00:00
-- url     : https://prove2.me/submissions/b3a02a8f-c63e-4dc6-9400-a18b5b06d3d1

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
theorem _root_.solution (k : ℕ) (ρ r : ℝ)
    (h : 0 < Real.sqrt (ρ ^ 2 + r ^ 2)) :
    facetAcceptanceProbability k ρ r = uniformSphere (Euc (k + 1))
      {v | ⟪(EuclideanSpace.basisFun (Fin (k + 1)) ℝ 0), v.val⟫_ℝ <
        ρ / Real.sqrt (ρ ^ 2 + r ^ 2)} := by
  unfold facetAcceptanceProbability
  congr 1
  ext v
  simp only [mem_ofPred_eq, real_inner_smul_left]
  rw [lt_div_iff₀ h, mul_comm]
end GaussianPerimeter
