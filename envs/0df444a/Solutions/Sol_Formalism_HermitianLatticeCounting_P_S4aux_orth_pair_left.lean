-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.orth_pair_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:04:30.075284+00:00
-- url     : https://prove2.me/submissions/2503c1b9-91eb-491e-8305-1af278b219bd

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
    h (∑ i, w i • v i) x = ∑ i, w i * h (v i) x := by
  rw [map_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
end Formalism.HermitianLatticeCounting.P.S4aux
