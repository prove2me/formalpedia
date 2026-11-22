-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.Part2.inTh_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:27:48.371943+00:00
-- url     : https://prove2.me/submissions/6c6da5bd-f0cd-4164-9197-cead72b1c5f4

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
theorem _root_.solution {E V : Type} [CommRing E] [AddCommGroup V] [Module E V] {th : E} {abelian₂ : AddSubgroup V} {a b : V}
    (ha : InTh th abelian₂ a) (hb : InTh th abelian₂ b) : InTh th abelian₂ (a + b) := by
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨y, hy, rfl⟩ := hb
  exact ⟨x + y, abelian₂.add_mem hx hy, (smul_add _ _ _).symm⟩
end Formalism.HermitianLatticeCounting.P.S4aux.Part2
