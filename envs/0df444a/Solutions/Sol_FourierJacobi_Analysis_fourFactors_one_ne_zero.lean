-- Prove2me | solution 1 for FourierJacobi.Analysis.fourFactors_one_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:37:45.94061+00:00
-- url     : https://prove2.me/submissions/d1978026-d1d1-4660-a514-8c4ecb339a10

import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_PaperDomain
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val



set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra
namespace FourierJacobi.Analysis
theorem _root_.solution (a b : ℂ) (ha : a ≠ 1) (hb : b ≠ 1) :
    fourFactors a b 1 ≠ 0 := by
  have hai : a⁻¹ ≠ 1 := by simpa using ha
  have hbi : b⁻¹ ≠ 1 := by simpa using hb
  simp only [fourFactors, mul_one]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero
    (sub_ne_zero.mpr ha.symm) (sub_ne_zero.mpr hai.symm))
    (sub_ne_zero.mpr hb.symm)) (sub_ne_zero.mpr hbi.symm)
end FourierJacobi.Analysis
