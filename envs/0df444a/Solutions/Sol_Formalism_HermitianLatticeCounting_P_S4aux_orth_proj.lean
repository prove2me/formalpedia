-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.orth_proj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:29:35.440117+00:00
-- url     : https://prove2.me/submissions/8135bdc9-2e68-4155-af43-1b79ada821d7

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_orth_pair_left

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
    (u : κ → Oˣ) (hu : ∀ i, (u i : O) = h (v i) (v i)) (x : abelian₂) (j : κ) :
    h (x - ∑ i, (h x (v i) * ((u i)⁻¹ : Oˣ)) • v i) (v j) = 0 := by
  rw [map_sub, LinearMap.sub_apply, orth_pair_left, Finset.sum_eq_single j]
  · rw [← hu, mul_assoc, Units.inv_mul, mul_one, sub_self]
  · intro i _ hi
    rw [horth i j hi, mul_zero]
  · intro hj; exact absurd (Finset.mem_univ _) hj
end Formalism.HermitianLatticeCounting.P.S4aux
