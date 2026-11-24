-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.not_unit_of_mem_mO
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:17.775855+00:00
-- url     : https://prove2.me/submissions/f58b98ab-84c3-46ef-a576-cb8a1ebd185f

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_mO_ne_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O]
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution (hU : Unram o O) (x : O) (hx : x ∈ mO o O) : ¬ IsUnit x := by
  rintro ⟨u, rfl⟩
  apply mO_ne_top hU
  have := Ideal.mul_mem_left (mO o O) ((u⁻¹ : Oˣ) : O) hx
  rwa [Units.inv_mul] at this
end Formalism.HermitianLatticeCounting.P.S4aux
