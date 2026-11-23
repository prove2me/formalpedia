-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.orth_pair_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:23.042014+00:00
-- url     : https://prove2.me/submissions/fb15054f-1958-46f6-b7f6-9c337a824f2d

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
theorem _root_.solution {κ : Type} [Fintype κ] (v : κ → abelian₂) (horth : ∀ i j, i ≠ j → h (v i) (v j) = 0)
    (j : κ) (w : κ → O) : h (v j) (∑ i, w i • v i) = star (w j) * h (v j) (v j) := by
  rw [map_sum, Finset.sum_eq_single j]
  · rw [LinearMap.map_smulₛₗ, starRingEnd_apply, smul_eq_mul]
  · intro i _ hi
    rw [LinearMap.map_smulₛₗ, horth j i (Ne.symm hi), smul_zero]
  · intro hj; exact absurd (Finset.mem_univ _) hj
end Formalism.HermitianLatticeCounting.P.S4aux
