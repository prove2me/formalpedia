-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.type_class_count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:27.037807+00:00
-- url     : https://prove2.me/submissions/6f3e85a3-a9d3-4b54-95e8-c5b58cebb89b

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
theorem _root_.solution : TypeBeClass := by
  intro E _ _ V _ _ h O abelian₂ th x x' hth hI ⟨w, hw, he⟩
  refine ⟨fun xi hxi h0 => ?_, fun xi hxi h0 => ?_⟩
  · have e : h xi x' = h xi (x + x') := by simp [h0]
    exact ⟨e, h xi w, hI _ hxi _ hw, by rw [e, he, LinearMap.map_smulₛₗ, starRingEnd_apply, hth]; rfl⟩
  · have e : h x xi = h (x + x') xi := by simp [h0]
    exact ⟨e, h w xi, hI _ hw _ hxi, by rw [e, he]; simp⟩
end Formalism.HermitianLatticeCounting.P.S4aux
