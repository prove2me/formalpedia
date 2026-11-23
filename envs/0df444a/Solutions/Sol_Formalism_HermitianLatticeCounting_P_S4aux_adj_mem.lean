-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.adj_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:58.937796+00:00
-- url     : https://prove2.me/submissions/cc6721b9-be49-4e48-afcc-2309be34bd1b

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
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution {E : Type} [CommRing E] (O : Subring E) (m : ℕ) (G : Matrix (Fin m) (Fin m) E)
    (hG : ∀ i j, G i j ∈ O) : ∀ i j, G.adjugate i j ∈ O := by
  intro i j
  let M : Matrix (Fin m) (Fin m) O := Matrix.of fun a b => ⟨G a b, hG a b⟩
  have : G = M.map O.subtype := by ext a b; rfl
  rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_adjugate]
  exact (M.adjugate i j).2
end Formalism.HermitianLatticeCounting.P.S4aux
