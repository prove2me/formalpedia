-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.orth_pair_gen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:06:34.312624+00:00
-- url     : https://prove2.me/submissions/770a1fcc-8cbe-45d6-82a7-89893a0e3539

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
variable {O : Type} [CommRing O] [StarRing O] {abelian₂ : Type} [AddCommGroup abelian₂] [Module O abelian₂]
  (h : abelian₂ →ₗ[O] abelian₂ →ₗ⋆[O] O)
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution {κ : Type} [Fintype κ] (v : κ → abelian₂) (x : abelian₂) (w : κ → O) :
    h x (∑ i, w i • v i) = ∑ i, star (w i) * h x (v i) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [LinearMap.map_smulₛₗ, starRingEnd_apply, smul_eq_mul]
end Formalism.HermitianLatticeCounting.P.S4aux
