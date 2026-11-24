-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.exists_unit_vec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:32.796132+00:00
-- url     : https://prove2.me/submissions/0a8ba39f-e727-4f02-87a5-f07865335985

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_not_unit_of_mem_mO
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_polar_mO
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_exists_unit_vec_gen

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
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O] {abelian₂ : Type} [AddCommGroup abelian₂] [Module O abelian₂] [Module.Free O abelian₂]
  [Module.Finite O abelian₂] (h : abelian₂ →ₗ[O] abelian₂ →ₗ⋆[O] O)
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution (hU : Unram o O) (hSD : SelfDual h) {κ : Type} [Fintype κ] (v : κ → abelian₂)
    (horth : ∀ i j, i ≠ j → h (v i) (v j) = 0) (hunit : ∀ i, IsUnit (h (v i) (v i)))
    (hk : Fintype.card κ < Module.finrank O abelian₂) : ∃ c, (∀ i, h c (v i) = 0) ∧ IsUnit (h c c) := by
  have : Nontrivial O := Module.nontrivial_of_finrank_pos (R := o) (by rw [hU.rank2]; norm_num)
  exact exists_unit_vec_gen h (mO o O) (not_unit_of_mem_mO hU) (polar_mO hU h hSD.1) hSD v horth hunit hk
end Formalism.HermitianLatticeCounting.P.S4aux
