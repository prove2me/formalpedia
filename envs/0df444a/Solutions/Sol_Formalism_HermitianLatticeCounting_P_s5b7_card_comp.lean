-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s5b7_card_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:50.156283+00:00
-- url     : https://prove2.me/submissions/a9da9f84-eb24-44d8-8a44-3badbcc6e552

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MeasurePreservingPiCompProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Module
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {R A B C : Type*} [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B]
    [Module R B] [AddCommGroup C] [Module R C] (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hg : Function.Injective g) :
    Nat.card (C ⧸ LinearMap.range (g ∘ₗ f)) =
      Nat.card (B ⧸ LinearMap.range f) * Nat.card (C ⧸ LinearMap.range g) := by
  set T := LinearMap.range (g ∘ₗ f) with hT
  have hTS : T ≤ LinearMap.range g := by
    rw [hT, LinearMap.range_comp]; exact LinearMap.map_le_range
  rw [← Submodule.card_quotient_mul_card_quotient (LinearMap.range g) T hTS]
  congr 1
  let h : B →ₗ[R] C ⧸ T := T.mkQ ∘ₗ g
  have hker : LinearMap.ker h = LinearMap.range f := by
    ext x
    simp only [h, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, hT, LinearMap.mem_range]
    constructor
    · rintro ⟨a, ha⟩; exact ⟨a, hg ha⟩
    · rintro ⟨a, rfl⟩; exact ⟨a, rfl⟩
  have hrange : LinearMap.range h = (LinearMap.range g).map T.mkQ := LinearMap.range_comp _ _
  exact Nat.card_congr (((Submodule.quotEquivOfEq _ _ hker.symm).trans h.quotKerEquivRange).trans
    (LinearEquiv.ofEq _ _ hrange)).symm.toEquiv
end Formalism.HermitianLatticeCounting.P
