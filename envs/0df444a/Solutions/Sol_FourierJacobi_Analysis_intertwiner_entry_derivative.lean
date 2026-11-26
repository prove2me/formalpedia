-- Prove2me | solution 1 for FourierJacobi.Analysis.intertwiner_entry_derivative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:50:23.109715+00:00
-- url     : https://prove2.me/submissions/6731244d-0c7e-4195-8633-cea6c5e5bbb8

import Definitions.Def_FourierJacobi_Algebra_Intertwiner
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Definitions.Def_FourierJacobi_Analysis_IntertwinerDerivative
import Theorems.Thm_FourierJacobi_Analysis_inducingPower_endpoint
import Theorems.Thm_FourierJacobi_Analysis_hasDerivAt_inducingPower

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Analysis
namespace FourierJacobi.Analysis
theorem _root_.solution (q : ℝ) (hq : 1 < q) (i j : Fin 2) :
    HasDerivAt (fun s => intertwinerFamily q s i j)
      ((-2 * Real.log q / (q - 1)) * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j) (1 / 2) := by
  have hq₀ : 0 < q := by linarith
  have hqne : q ≠ 0 := ne_of_gt hq₀
  have hq₁ : q - 1 ≠ 0 := by linarith
  have hr : inducingPower q (1 / 2) = q⁻¹ := inducingPower_endpoint q hq₀
  have hden : 1 - inducingPower q (1 / 2) ≠ 0 := by
    rw [hr]
    exact sub_ne_zero.mpr (Ne.symm (inv_ne_one.mpr (by linarith)))
  have hp := hasDerivAt_inducingPower q hq₀
  have hb := hp.const_sub 1
  have hc := hasDerivAt_const (1 / 2 : ℝ) (1 - q⁻¹)
  have h00 := (hc.mul hp).div hb hden
  have h11 := hc.div hb hden
  simp only [Pi.mul_apply, hr, zero_mul, zero_add, zero_sub] at h00 h11
  clear hp hb hc hden hr
  fin_cases i <;> fin_cases j
  · convert h00 using 1 <;> first | rfl | (norm_num; field_simp; ring)
  · simpa [intertwinerFamily, intertwinerMatrix] using hasDerivAt_const (1 / 2 : ℝ) (1 : ℝ)
  · simpa [intertwinerFamily, intertwinerMatrix] using hasDerivAt_const (1 / 2 : ℝ) q⁻¹
  · convert h11 using 1 <;> first | rfl | (norm_num; field_simp)
end FourierJacobi.Analysis
