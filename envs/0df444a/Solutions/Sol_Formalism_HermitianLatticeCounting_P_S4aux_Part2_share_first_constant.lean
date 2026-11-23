-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.Part2.share_first_constant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:59.046809+00:00
-- url     : https://prove2.me/submissions/62c1e008-5246-49b5-b52d-9c17b7eed609

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
open Formalism.HermitianLatticeCounting.P.S4aux.Part2
namespace Formalism.HermitianLatticeCounting.P.S4aux.Part2
theorem _root_.solution : LocalDensityShareBound := by
  intro Ov _ dens dl κ be disc tot k r hk hκ hbe hcard hdens hdl htot
  have hbe0 : (0 : ℝ) < be := by linarith
  have hpow : (be ^ (k + 2 * r + 1))⁻¹ / (be ^ (2 * r + 2))⁻¹ = (be ^ (k - 1))⁻¹ := by
    obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le hk
    have : 1 + k' + 2 * r + 1 = k' + (2 * r + 2) := by ring
    rw [this, pow_add, Nat.add_sub_cancel_left]
    field_simp
  have hB : 0 ≤ (be ^ (k - 1))⁻¹ := by positivity
  calc ∑ M, dens M ≤ ∑ _M : Ov, κ * (be ^ (k - 1))⁻¹ * 2 := by
        refine Finset.sum_le_sum fun M _ => ?_
        rw [hdens M, hpow]
        exact mul_le_mul_of_nonneg_left (hdl M) (mul_nonneg hκ hB)
    _ = (Fintype.card Ov : ℝ) * (κ * (be ^ (k - 1))⁻¹ * 2) := by simp
    _ ≤ disc ^ (2 * r + 2) * (κ * (be ^ (k - 1))⁻¹ * 2) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 4 * disc ^ (2 * r + 2) * (be ^ (k - 1))⁻¹ * (κ / 2) := by ring
    _ ≤ 4 * disc ^ (2 * r + 2) * (be ^ (k - 1))⁻¹ * tot := by
        refine mul_le_mul_of_nonneg_left htot ?_
        have : (0 : ℝ) ≤ disc ^ (2 * r + 2) := le_trans (Nat.cast_nonneg _) hcard
        positivity
end Formalism.HermitianLatticeCounting.P.S4aux.Part2
