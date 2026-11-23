-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.Part2.sum_mem_lat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:00:45.014151+00:00
-- url     : https://prove2.me/submissions/d4b05c10-b148-4e0f-a2ac-f43789e8b48b

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
theorem _root_.solution {E V : Type} [CommRing E] [AddCommGroup V] [Module E V] {O : Subring E} {abelian₂ : AddSubgroup V}
    (hL : IsLat O abelian₂) {n : ℕ} {f : Fin n → V} {a : Fin n → E} (hf : ∀ i, f i ∈ abelian₂) (ha : ∀ i, a i ∈ O) :
    (∑ i, a i • f i) ∈ abelian₂ := abelian₂.sum_mem fun i _ => hL _ (ha i) _ (hf i)
end Formalism.HermitianLatticeCounting.P.S4aux.Part2
