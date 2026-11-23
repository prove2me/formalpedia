-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.Part2.inTh_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:58.100435+00:00
-- url     : https://prove2.me/submissions/968156c7-661f-422c-b4b2-1a0f2e703443

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
theorem _root_.solution {E V : Type} [CommRing E] [AddCommGroup V] [Module E V] {O : Subring E} {th c : E}
    {abelian₂ : AddSubgroup V} {a : V} (hL : IsLat O abelian₂) (hc : c ∈ O) (ha : InTh th abelian₂ a) : InTh th abelian₂ (c • a) := by
  obtain ⟨x, hx, rfl⟩ := ha
  exact ⟨c • x, hL c hc x hx, smul_comm _ _ _⟩
end Formalism.HermitianLatticeCounting.P.S4aux.Part2
