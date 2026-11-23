-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.gauss_summand_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:01:10.335322+00:00
-- url     : https://prove2.me/submissions/2bde73ec-e446-4d76-ba39-75bf13007b7e

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_cast
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_cast
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_last



set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution : GaussSummand := by
  intro U₀ U₁ _ _ φ₀ φ₁ h
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, norm_mul]
  gcongr
  calc ‖∑ u, φ₁ u‖ ≤ ∑ u, ‖φ₁ u‖ := norm_sum_le _ _
    _ ≤ ∑ u : U₁, (1:ℝ) := Finset.sum_le_sum (fun u _ => h u)
    _ = _ := by simp
end Formalism.HermitianLatticeCounting.P.S4aux
