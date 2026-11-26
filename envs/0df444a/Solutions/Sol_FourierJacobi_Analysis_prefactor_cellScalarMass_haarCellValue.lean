-- Prove2me | solution 1 for FourierJacobi.Analysis.prefactor_cellScalarMass_haarCellValue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:51:17.428401+00:00
-- url     : https://prove2.me/submissions/0ab17915-2421-413f-840b-e5e95bcfcc7e

import Definitions.Def_FourierJacobi_Analysis_HaarCellValue
import Definitions.Def_FourierJacobi_Analysis_HaarCellMass
import Definitions.Def_FourierJacobi_Analysis_HaarCellMaster
import Theorems.Thm_FourierJacobi_Algebra_inverseSqrt_pos
import Theorems.Thm_FourierJacobi_Analysis_coreCentral_one
import Theorems.Thm_FourierJacobi_Analysis_coreCentral_two
import Theorems.Thm_FourierJacobi_Analysis_coreCentral_zero
import Theorems.Thm_FourierJacobi_Analysis_coreIntegralPrefactor_mul_shell_volume
import Theorems.Thm_FourierJacobi_Analysis_coreScaleExponent_coe
import Theorems.Thm_FourierJacobi_Analysis_haarCellValue_expanded
import Theorems.Thm_FourierJacobi_Analysis_haar_shell_zpow_coe
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
import Theorems.Thm_FourierJacobi_Analysis_inverseSqrt_coe_sq
import Theorems.Thm_FourierJacobi_Analysis_masterTerm_zero
import Theorems.Thm_FourierJacobi_Analysis_paperC_eq_poincare
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
theorem _root_.solution (q : ℝ) (hq : 1 < q)
    (a b d : ℂ) (T : ℝ) (hT : T ≠ 0) (r : Fin 3) (i : LatticeIndex) :
    coreIntegralPrefactor q r * haarCellScalarMass q (r.val : ℤ) i *
        haarCellValue q a b d T (r.val : ℤ) i =
      ∑ w : Fin 8, (weylWeights (inverseSqrt q : ℂ) a b w / paperC q) *
        masterTerm (q : ℂ) (inverseSqrt q : ℂ) d (weylU a b w) (weylV a b w)
          (T : ℂ) (r.val : ℤ) i := by
  have hq₀ : 0 < q := by linarith
  have ht : (inverseSqrt q : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (inverseSqrt_pos hq)
  unfold haarCellScalarMass
  calc
    _ = (coreIntegralPrefactor q r * (1 - (q : ℂ)⁻¹) ^ 3) *
        (((q : ℂ) ^ (-i.2.1) * (q : ℂ) ^ (-i.2.2.1)) *
          collisionWeight (q : ℂ) (r.val : ℤ) i.2.1 i.2.2.1 i.2.2.2 *
          haarCellValue q a b d T (r.val : ℤ) i) := by ring
    _ = (shellCoeff (q : ℂ) (r.val : ℤ) * (1 - (q : ℂ)⁻¹) ^ 2) *
        (((q : ℂ) ^ (-i.2.1) * (q : ℂ) ^ (-i.2.2.1)) *
          collisionWeight (q : ℂ) (r.val : ℤ) i.2.1 i.2.2.1 i.2.2.2 *
          haarCellValue q a b d T (r.val : ℤ) i) := by
      rw [coreIntegralPrefactor_mul_shell_volume q hq r]
    _ = _ := by
      rw [haarCellValue_expanded q hq₀ a b d T hT (r.val : ℤ) i,
        haar_shell_zpow_coe q hq₀.le i.2.1, haar_shell_zpow_coe q hq₀.le i.2.2.1,
        paperC_eq_poincare q hq₀.le, ← inverseSqrt_coe_sq q hq₀.le]
      simp only [mul_assoc, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      unfold masterTerm shellMonomial
      dsimp
      simp only [zpow_add₀ ht, div_eq_mul_inv]
      ring
end FourierJacobi.Analysis
