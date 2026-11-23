-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.frob_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:00:46.677473+00:00
-- url     : https://prove2.me/submissions/09d6bde3-efe7-4352-b065-dc69a13bc63f

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance

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
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution {ι : Type} (s : Finset ι) (f : ι → L) :
    (∑ i ∈ s, f i) ^ Fintype.card K = ∑ i ∈ s, f i ^ Fintype.card K :=
  map_sum (FiniteField.frobeniusAlgHom K L) f s
end Formalism.HermitianLatticeCounting.P.S4aux
