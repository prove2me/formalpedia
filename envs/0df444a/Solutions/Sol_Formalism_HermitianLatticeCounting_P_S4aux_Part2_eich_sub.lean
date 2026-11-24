-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.Part2.eich_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:20.406008+00:00
-- url     : https://prove2.me/submissions/998c4f43-d28a-4c1e-b009-7e38ad07b96c

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
open Formalism.HermitianLatticeCounting.P.S4aux.Part2
namespace Formalism.HermitianLatticeCounting.P.S4aux.Part2
theorem _root_.solution {E V : Type} [CommRing E] [StarRing E] [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (x u : V) (s : E) (v w : V) :
    eich h x u s (v - w) = eich h x u s v - eich h x u s w := (eichLin h x u s).map_sub v w
end Formalism.HermitianLatticeCounting.P.S4aux.Part2
