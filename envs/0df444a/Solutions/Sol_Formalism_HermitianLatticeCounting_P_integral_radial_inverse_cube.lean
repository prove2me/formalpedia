-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.integral_radial_inverse_cube
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:32.260375+00:00
-- url     : https://prove2.me/submissions/19d21fd1-6070-4bd9-a759-eb4e4a2eccdd

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SchurAverage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open InnerProductSpace
open MeasureTheory Set
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (H : ℝ) (hH : 0 < H) :
    IntegrableOn (fun y : ℝ => y * ((max 1 (y / H)) ^ 3)⁻¹) (Ioi 0) ∧
      ∫ y in Ioi (0:ℝ), y * ((max 1 (y / H)) ^ 3)⁻¹ = 3 * H ^ 2 / 2 := by
  have hsplit : Ioi (0:ℝ) = Ioc 0 H ∪ Ioi H := (Ioc_union_Ioi_eq_Ioi hH.le).symm
  have e1 : EqOn (fun y : ℝ => y * ((max 1 (y / H)) ^ 3)⁻¹) (fun y => y) (Ioc 0 H) := by
    intro y hy
    have : y / H ≤ 1 := by rw [div_le_one hH]; exact hy.2
    simp only [max_eq_left this]; norm_num
  have e2 : EqOn (fun y : ℝ => y * ((max 1 (y / H)) ^ 3)⁻¹) (fun y => H ^ 3 * y ^ (-2 : ℝ)) (Ioi H) := by
    intro y hy
    have hy' : H < y := hy
    have hy0 : 0 < y := by linarith
    have : 1 ≤ y / H := by rw [le_div_iff₀ hH]; linarith
    simp only [max_eq_right this]
    rw [Real.rpow_neg hy0.le, Real.rpow_two]
    field_simp
  have i1 : IntegrableOn (fun y : ℝ => y * ((max 1 (y / H)) ^ 3)⁻¹) (Ioc 0 H) := by
    rw [integrableOn_congr_fun e1 measurableSet_Ioc]
    exact (continuous_id.integrableOn_Icc (a := 0) (b := H)).mono_set Ioc_subset_Icc_self
  have i2 : IntegrableOn (fun y : ℝ => y * ((max 1 (y / H)) ^ 3)⁻¹) (Ioi H) := by
    rw [integrableOn_congr_fun e2 measurableSet_Ioi]
    exact (integrableOn_Ioi_rpow_of_lt (by norm_num) hH).const_mul _
  refine ⟨by rw [hsplit]; exact i1.union i2, ?_⟩
  rw [hsplit, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi i1 i2,
    setIntegral_congr_fun measurableSet_Ioc e1, setIntegral_congr_fun measurableSet_Ioi e2,
    integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hH,
    ← intervalIntegral.integral_of_le hH.le, integral_id]
  have : H ^ ((-2:ℝ) + 1) = H⁻¹ := by
    rw [show (-2:ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
  rw [this]; field_simp; ring
end Formalism.HermitianLatticeCounting.P
