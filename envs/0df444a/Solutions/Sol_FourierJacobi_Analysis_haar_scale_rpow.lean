-- Prove2me | solution 1 for FourierJacobi.Analysis.haar_scale_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:46:14.193964+00:00
-- url     : https://prove2.me/submissions/8ddca42e-87b2-4e34-8277-cd78d69462df

import Definitions.Def_FourierJacobi_Analysis_HaarLatticePartition
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_HaarCellValue
import Theorems.Thm_FourierJacobi_Analysis_coreCentral_one
import Theorems.Thm_FourierJacobi_Analysis_coreCentral_two
import Theorems.Thm_FourierJacobi_Analysis_coreCentral_zero
import Theorems.Thm_FourierJacobi_Analysis_coreScaleExponent_coe
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
import Theorems.Thm_FourierJacobi_Analysis_inverseSqrt_even_zpow
import Theorems.Thm_FourierJacobi_Analysis_masterTerm_zero
import Theorems.Thm_FourierJacobi_Analysis_shellMonomial_zero
import Theorems.Thm_FourierJacobi_Valuations_actualEntryInteger_coe
import Theorems.Thm_FourierJacobi_Valuations_actualMinorInteger_coe
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_zero
attribute [local simp] FourierJacobi.Analysis.coreCentral_one
attribute [local simp] FourierJacobi.Analysis.coreCentral_two
attribute [local simp] FourierJacobi.Analysis.coreCentral_zero
attribute [local simp] FourierJacobi.Analysis.coreScaleExponent_coe
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.masterTerm_zero
attribute [local simp] FourierJacobi.Analysis.shellMonomial_zero
attribute [local simp] FourierJacobi.Valuations.actualEntryInteger_coe
attribute [local simp] FourierJacobi.Valuations.actualMinorInteger_coe
attribute [local simp] FourierJacobi.Valuations.localFieldValuation_zero



set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra FourierJacobi.Valuations
set_option maxHeartbeats 2000000
namespace FourierJacobi.Analysis
theorem _root_.solution (q : ℝ) (hq : 0 < q) (k : ℤ) :
    Real.rpow (q ^ (-k)) (3 / 2) = inverseSqrt q ^ (3 * k) := by
  have ht : 0 ≤ inverseSqrt q := inv_nonneg.mpr (Real.sqrt_nonneg q)
  rw [← inverseSqrt_even_zpow q hq.le k]
  calc
    Real.rpow (inverseSqrt q ^ (2 * k)) (3 / 2) =
        inverseSqrt q ^ (((2 * k : ℤ) : ℝ) * (3 / 2 : ℝ)) := by
      simpa only [Real.rpow_eq_pow, Real.rpow_intCast] using
        (Real.rpow_mul ht (((2 * k : ℤ) : ℝ)) (3 / 2 : ℝ)).symm
    _ = inverseSqrt q ^ (3 * k) := by
      have he : ((2 * k : ℤ) : ℝ) * (3 / 2 : ℝ) = ((3 * k : ℤ) : ℝ) := by
        push_cast
        ring
      rw [he, Real.rpow_intCast]
end FourierJacobi.Analysis
