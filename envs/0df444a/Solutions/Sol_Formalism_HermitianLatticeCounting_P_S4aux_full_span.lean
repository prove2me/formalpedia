-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.full_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:38.911506+00:00
-- url     : https://prove2.me/submissions/32288e23-e9a1-4935-b9d5-493749d51ea2

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_span_orthogonal_unit_basis_eq_top

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
omit [IsDomain o] [IsDiscreteValuationRing o] [Algebra o O] [CommRing o]
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution [Nontrivial O] {κ : Type} [Fintype κ] (v : κ → abelian₂)
    (horth : ∀ i j, i ≠ j → h (v i) (v j) = 0) (hunit : ∀ i, IsUnit (h (v i) (v i)))
    (hcard : Fintype.card κ = Module.finrank O abelian₂) : Submodule.span O (Set.range v) = ⊤ := by
  have e : Module.Free.ChooseBasisIndex O abelian₂ ≃ κ := Fintype.equivOfCardEq (by
    rw [hcard, Module.finrank_eq_card_chooseBasisIndex])
  have := span_orthogonal_unit_basis_eq_top h (v ∘ e) (fun i j hij => horth _ _ (fun hh => hij (e.injective hh)))
    (fun i => hunit _)
  rwa [e.surjective.range_comp] at this
end Formalism.HermitianLatticeCounting.P.S4aux
