-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.Part2.eich_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:28.97827+00:00
-- url     : https://prove2.me/submissions/e7bd841f-a31e-42ad-8dcb-3b65b1bb325e

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
    (h : V →ₗ[E] V →ₗ⋆[E] E) (x u : V) (s c : E) (v : V) :
    eich h x u s (c • v) = c • eich h x u s v := (eichLin h x u s).map_smul c v
end Formalism.HermitianLatticeCounting.P.S4aux.Part2
