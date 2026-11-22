-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.trace_surj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:29:38.422386+00:00
-- url     : https://prove2.me/submissions/bcbcf96f-0d84-4cf1-9135-5406eef15ab9

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
theorem _root_.solution : Function.Surjective (Algebra.trace K L) := by
  have : FiniteDimensional K L := Module.Finite.of_finite
  exact Algebra.trace_surjective K L
end Formalism.HermitianLatticeCounting.P.S4aux
