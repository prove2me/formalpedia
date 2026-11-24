-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.SupplyAP.excTerm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:32.892081+00:00
-- url     : https://prove2.me/submissions/81d67065-0060-48c0-b0c1-7fac94f1aa6b

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_ExcTerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.SupplyAP
namespace Formalism.HermitianLattices.Ext.SupplyAP
theorem _root_.solution (x β : ℝ) (hx : 0 < x) (hL : 4 ≤ Real.log x) (hβ1 : 1 / 2 ≤ β) (hβ2 : β ≤ 1) :
    x ^ β / β ≤ x * (1 - (1 - β) / 2) := by
  have hβpos : 0 < β := by linarith
  have hsplit : x ^ β = x * x ^ (β - 1) := by
    rw [Real.rpow_sub hx, Real.rpow_one]
    field_simp
  have hy0 : 0 ≤ x ^ (β - 1) := Real.rpow_nonneg hx.le _
  have hyE : x ^ (β - 1) * Real.exp (4 * (1 - β)) ≤ 1 := by
    rw [Real.rpow_def_of_pos hx, ← Real.exp_add]
    have hneg : Real.log x * (β - 1) + 4 * (1 - β) ≤ 0 := by nlinarith
    calc Real.exp (Real.log x * (β - 1) + 4 * (1 - β)) ≤ Real.exp 0 := Real.exp_le_exp.mpr hneg
      _ = 1 := Real.exp_zero
  have hE := Real.add_one_le_exp (4 * (1 - β))
  have hPpos : 0 ≤ β * (1 - (1 - β) / 2) := mul_nonneg hβpos.le (by linarith)
  have hP : 1 ≤ (4 * (1 - β) + 1) * (β * (1 - (1 - β) / 2)) := by
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hβ2) (sub_nonneg.2 hβ1))
      (by linarith : (0:ℝ) ≤ 5 / 2 + 2 * β), sub_nonneg.2 hβ2]
  have hEP : 1 ≤ Real.exp (4 * (1 - β)) * (β * (1 - (1 - β) / 2)) :=
    le_trans hP (mul_le_mul_of_nonneg_right hE hPpos)
  have hyP : x ^ (β - 1) ≤ β * (1 - (1 - β) / 2) := by
    calc x ^ (β - 1) = x ^ (β - 1) * 1 := (mul_one _).symm
      _ ≤ x ^ (β - 1) * (Real.exp (4 * (1 - β)) * (β * (1 - (1 - β) / 2))) :=
          mul_le_mul_of_nonneg_left hEP hy0
      _ = (x ^ (β - 1) * Real.exp (4 * (1 - β))) * (β * (1 - (1 - β) / 2)) := by ring
      _ ≤ 1 * (β * (1 - (1 - β) / 2)) := mul_le_mul_of_nonneg_right hyE hPpos
      _ = β * (1 - (1 - β) / 2) := one_mul _
  rw [hsplit, div_le_iff₀ hβpos]
  calc x * x ^ (β - 1) ≤ x * (β * (1 - (1 - β) / 2)) := mul_le_mul_of_nonneg_left hyP hx.le
    _ = x * (1 - (1 - β) / 2) * β := by ring
end Formalism.HermitianLattices.Ext.SupplyAP
