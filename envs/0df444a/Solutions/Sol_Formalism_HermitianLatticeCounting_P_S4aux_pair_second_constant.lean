-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.pair_second_constant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:23.22655+00:00
-- url     : https://prove2.me/submissions/5c36ae68-5435-49da-b610-b42ae4f3f660

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
theorem _root_.solution : PairingOrthogonalComplement := by
  intro E _ _ V _ _ h O abelian₂ th w1 la1 la2 la2' hth hI h1 h2 h3
  have key : h la1 la2' = h (w1 + la1) (la2' - la2) := by
    simp only [map_add, map_sub, LinearMap.add_apply, h1, h2, h3]; ring
  refine ⟨key, ?_⟩
  rintro hw ⟨w, hw', he⟩
  refine ⟨h (w1 + la1) w, hI _ hw _ hw', ?_⟩
  rw [key, he, LinearMap.map_smulₛₗ, starRingEnd_apply, hth]; rfl
end Formalism.HermitianLatticeCounting.P.S4aux
