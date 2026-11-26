-- Prove2me | solution 1 for FourierJacobi.Analysis.haarCellValue_expanded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:49:12.601829+00:00
-- url     : https://prove2.me/submissions/f4a2dda5-aec5-4fba-a03e-049ba8186935

import Definitions.Def_FourierJacobi_Analysis_HaarLatticePartition
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_HaarCellValue
import Theorems.Thm_FourierJacobi_Analysis_haar_scale_rpow_coe
import Theorems.Thm_FourierJacobi_Analysis_coreCentral_one
import Theorems.Thm_FourierJacobi_Analysis_coreCentral_two
import Theorems.Thm_FourierJacobi_Analysis_coreCentral_zero
import Theorems.Thm_FourierJacobi_Analysis_coreScaleExponent_coe
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
import Theorems.Thm_FourierJacobi_Analysis_masterTerm_zero
import Theorems.Thm_FourierJacobi_Analysis_shellMonomial_zero
import Theorems.Thm_FourierJacobi_Analysis_shell_height_eq
import Theorems.Thm_FourierJacobi_Analysis_weylKernelAtIndices_damping
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
theorem _root_.solution (q : ℝ) (hq : 0 < q) (a b d : ℂ)
    (T : ℝ) (hT : T ≠ 0) (r : ℤ) (i : LatticeIndex) :
    haarCellValue q a b d T r i =
      d ^ i.1 * (inverseSqrt q : ℂ) ^ (3 * i.1) *
        ((poincare (inverseSqrt q : ℂ))⁻¹ * ∑ w : Fin 8,
          weylWeights (inverseSqrt q : ℂ) a b w *
            (inverseSqrt q : ℂ) ^
              (3 * (cartanIndices r i.1 i.2.1 i.2.2.1 i.2.2.2).1 +
                4 * (cartanIndices r i.1 i.2.1 i.2.2.1 i.2.2.2).2) *
            ((T : ℂ) * weylU a b w) ^
              ((cartanIndices r i.1 i.2.1 i.2.2.1 i.2.2.2).1 / 2) *
            ((T : ℂ) * weylV a b w) ^
              (cartanIndices r i.1 i.2.1 i.2.2.1 i.2.2.2).2) := by
  have hT' : (T : ℂ) ≠ 0 := by exact_mod_cast hT
  have hH := (shell_height_eq r i.1 i.2.1 i.2.2.1 i.2.2.2).symm
  have he : 6 * ((cartanIndices r i.1 i.2.1 i.2.2.1 i.2.2.2).1 / 2) =
      3 * (cartanIndices r i.1 i.2.1 i.2.2.1 i.2.2.2).1 := by
    unfold cartanIndices
    dsimp
    omega
  unfold haarCellValue
  rw [haar_scale_rpow_coe q hq, hH, mul_assoc]
  rw [weylKernelAtIndices_damping _ _ _ _ _ _ hT']
  rw [he]
end FourierJacobi.Analysis
