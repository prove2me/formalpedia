-- Prove2me | solution 1 for FD1D.dyadicTent_sq_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:24:47.585137+00:00
-- url     : https://prove2.me/submissions/e04f4591-b711-45a5-bb20-f6bb5bc36369

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const


section
namespace FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
namespace DyadicMass
end DyadicMass
private theorem left_sq_integral (l p : ℝ) (hp : 0 < p) :
    (∫ z in l..l + p / 2, ((z - l) / p) ^ 2) = p / 24 := by
  have hpow : IntervalIntegrable (fun z : ℝ => z ^ 2) volume l (l + p / 2) :=
    (continuous_id.pow 2).intervalIntegrable _ _
  have hlin : IntervalIntegrable (fun z : ℝ => 2 * l * z) volume l (l + p / 2) :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have hconst : IntervalIntegrable (fun _ : ℝ => l ^ 2) volume l (l + p / 2) :=
    continuous_const.intervalIntegrable _ _
  rw [show (fun z : ℝ => ((z - l) / p) ^ 2) =
      fun z => ((z ^ 2 - 2 * l * z) + l ^ 2) / p ^ 2 by
    funext z
    ring]
  rw [intervalIntegral.integral_div]
  rw [intervalIntegral.integral_add (hpow.sub hlin) hconst]
  rw [intervalIntegral.integral_sub hpow hlin]
  rw [integral_pow]
  rw [intervalIntegral.integral_const_mul]
  rw [integral_id]
  rw [intervalIntegral.integral_const]
  field_simp
  ring
private theorem right_sq_integral (l p : ℝ) (hp : 0 < p) :
    (∫ z in l + p / 2..l + p, ((l + p - z) / p) ^ 2) = p / 24 := by
  have hpow : IntervalIntegrable (fun z : ℝ => z ^ 2) volume (l + p / 2) (l + p) :=
    (continuous_id.pow 2).intervalIntegrable _ _
  have hlin : IntervalIntegrable (fun z : ℝ => 2 * (l + p) * z)
      volume (l + p / 2) (l + p) :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have hconst : IntervalIntegrable (fun _ : ℝ => (l + p) ^ 2)
      volume (l + p / 2) (l + p) :=
    continuous_const.intervalIntegrable _ _
  rw [show (fun z : ℝ => ((l + p - z) / p) ^ 2) =
      fun z => ((z ^ 2 - 2 * (l + p) * z) + (l + p) ^ 2) / p ^ 2 by
    funext z
    ring]
  rw [intervalIntegral.integral_div]
  rw [intervalIntegral.integral_add (hpow.sub hlin) hconst]
  rw [intervalIntegral.integral_sub hpow hlin]
  rw [integral_pow]
  rw [intervalIntegral.integral_const_mul]
  rw [integral_id]
  rw [intervalIntegral.integral_const]
  field_simp
  ring
private theorem dyadicTent_sq_pointwise (l p z : ℝ) :
    dyadicTent l p z ^ 2 =
      (Icc l (l + p / 2)).indicator (fun x => ((x - l) / p) ^ 2) z +
      (Ioc (l + p / 2) (l + p)).indicator (fun x => ((l + p - x) / p) ^ 2) z := by
  by_cases hL : z ∈ Icc l (l + p / 2)
  · have hR : z ∉ Ioc (l + p / 2) (l + p) := by
      intro h
      linarith [hL.2, h.1]
    simp [dyadicTent, hL, hR]
  · by_cases hR : z ∈ Ioc (l + p / 2) (l + p)
    · simp [dyadicTent, hL, hR]
    · simp [dyadicTent, hL, hR]
namespace HaarTerm
end HaarTerm
namespace DyadicMass
end DyadicMass
namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]
end FiniteLaw
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
namespace DyadicMass
end DyadicMass
namespace MonotoneQuantilePolicy
end MonotoneQuantilePolicy
namespace FiniteLaw
end FiniteLaw
end
end FD1D
end

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
namespace FD1D
theorem _root_.solution (l p : ℝ) (hp : 0 < p) :
    (∫ z, dyadicTent l p z ^ 2) = p / 12 := by
  have hleft : IntegrableOn (fun z : ℝ => ((z - l) / p) ^ 2)
      (Icc l (l + p / 2)) :=
    ((continuous_id.sub continuous_const).div_const p |>.pow 2).integrableOn_Icc
  have hright : IntegrableOn (fun z : ℝ => ((l + p - z) / p) ^ 2)
      (Ioc (l + p / 2) (l + p)) :=
    ((continuous_const.sub continuous_id).div_const p |>.pow 2).integrableOn_Ioc
  rw [show (fun z : ℝ => dyadicTent l p z ^ 2) = fun z =>
      (Icc l (l + p / 2)).indicator (fun x => ((x - l) / p) ^ 2) z +
      (Ioc (l + p / 2) (l + p)).indicator
        (fun x => ((l + p - x) / p) ^ 2) z by
    funext z
    exact dyadicTent_sq_pointwise l p z]
  rw [MeasureTheory.integral_add (hleft.integrable_indicator measurableSet_Icc)
    (hright.integrable_indicator measurableSet_Ioc)]
  rw [MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_indicator measurableSet_Ioc]
  rw [integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (by linarith : l ≤ l + p / 2)]
  rw [← intervalIntegral.integral_of_le (by linarith : l + p / 2 ≤ l + p)]
  rw [left_sq_integral l p hp, right_sq_integral l p hp]
  ring
end FD1D
