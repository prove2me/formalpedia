-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.ncard_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:37.047275+00:00
-- url     : https://prove2.me/submissions/c79da2ad-0f67-4cc7-b8c5-5df4c5898d65

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_mem_orbit_sub
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
variable {G X : Type} [Group G] [MulAction G X]
open MulAction
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution (g : G) (x y : X) :
    (orbit (stabilizer G (g • y)) x).ncard = (orbit (stabilizer G y) (g⁻¹ • x)).ncard := by
  have : orbit (stabilizer G y) (g⁻¹ • x) = (fun w => g⁻¹ • w) '' orbit (stabilizer G (g • y)) x := by
    ext w
    simp only [Set.mem_image, mem_orbit_sub, mem_stabilizer_iff]
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨(g * k * g⁻¹) • x, ⟨g * k * g⁻¹, ?_, rfl⟩, ?_⟩
      · simp [mul_smul, hk]
      · simp [mul_smul]
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      refine ⟨g⁻¹ * k * g, ?_, ?_⟩
      · simp [mul_smul, hk]
      · simp [mul_smul]
  rw [this, Set.ncard_image_of_injective _ (MulAction.injective g⁻¹)]
end Formalism.HermitianLatticeCounting.P.S4aux
