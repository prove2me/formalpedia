-- Prove2me | solution 1 for FourierJacobi.Analysis.coreIntegralPrefactor_mul_shell_volume
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:46:47.292795+00:00
-- url     : https://prove2.me/submissions/1bf215fa-b51a-4681-b446-341ced37ed36

import Definitions.Def_FourierJacobi_Analysis_HaarLatticePartition
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_HaarCellValue
import Theorems.Thm_FourierJacobi_Analysis_norm_one_sub_ne_zero
import Theorems.Thm_FourierJacobi_Analysis_residue_inverse_norm_lt_one


set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra FourierJacobi.Valuations
set_option maxHeartbeats 2000000
namespace FourierJacobi.Analysis
theorem _root_.solution (q : ℝ) (hq : 1 < q) (r : Fin 3) :
    coreIntegralPrefactor q r * (1 - (q : ℂ)⁻¹) ^ 3 =
      shellCoeff (q : ℂ) (r.val : ℤ) * (1 - (q : ℂ)⁻¹) ^ 2 := by
  have hR : 1 - (q : ℂ)⁻¹ ≠ 0 :=
    norm_one_sub_ne_zero (residue_inverse_norm_lt_one q hq)
  fin_cases r
  · change (1 - (q : ℂ)⁻¹)⁻¹ * (1 - (q : ℂ)⁻¹) ^ 3 =
      (1 : ℂ) * (1 - (q : ℂ)⁻¹) ^ 2
    field_simp
  · change (q : ℂ) * (1 - (q : ℂ)⁻¹) ^ 3 =
      ((q : ℂ) * (1 - (q : ℂ)⁻¹)) * (1 - (q : ℂ)⁻¹) ^ 2
    ring
  · change (-(q : ℂ) / (1 - (q : ℂ)⁻¹)) * (1 - (q : ℂ)⁻¹) ^ 3 =
      -(q : ℂ) * (1 - (q : ℂ)⁻¹) ^ 2
    field_simp
end FourierJacobi.Analysis
