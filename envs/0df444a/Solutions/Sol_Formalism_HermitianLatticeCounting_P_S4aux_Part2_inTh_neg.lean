-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.Part2.inTh_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:20.848179+00:00
-- url     : https://prove2.me/submissions/bc39f230-aaf5-4cef-8b5d-884a4470673a

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
theorem _root_.solution {E V : Type} [CommRing E] [AddCommGroup V] [Module E V] {th : E} {abelian₂ : AddSubgroup V} {a : V}
    (ha : InTh th abelian₂ a) : InTh th abelian₂ (-a) := by
  obtain ⟨x, hx, rfl⟩ := ha
  exact ⟨-x, abelian₂.neg_mem hx, (smul_neg _ _).symm⟩
end Formalism.HermitianLatticeCounting.P.S4aux.Part2
