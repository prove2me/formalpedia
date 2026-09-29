-- Prove2me | solution 1 for CoalgHom.exists_addMonoidAlgebra_lift_residueField_of_henselianLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/7278c93a-f8aa-55e8-88b0-fea01d626754

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CharacterClosure
import Theorems.Thm_CartierDual_exists_coalgHom_addMonoidAlgebra_eq_sum_single_of_isIdempotentElem
import Theorems.Thm_CartierDual_exists_isIdempotentElem_eq_sum_single_of_coalgHom_addMonoidAlgebra
import Theorems.Thm_CartierDual_exists_ringHom_apply_eq_dualBaseChangeLin_tmul_of_isLocalRing
import Theorems.Thm_HenselianLocalRing_existsUnique_isIdempotentElem_mk_eq_of_moduleFinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CoalgHom_exists_addMonoidAlgebra_lift_residueField_of_henselianLocalRing

set_option autoImplicit false

universe u v w

open IsLocalRing
open scoped TensorProduct

namespace CoalgLiftHensel

variable {R : Type u} [CommRing R] [HenselianLocalRing R]
  {B : Type v} [CommRing B] [HopfAlgebra R B] [Module.Finite R B] [Module.Free R B] [Coalgebra.IsCocomm R B]

local notation "κ" => ResidueField R

section Lift

variable (r : CartierDual R B →+* CartierDual (ResidueField R) (ResidueField R ⊗[R] B))
  (hsurj : Function.Surjective r)
  (hker : RingHom.ker r = (maximalIdeal R).map (algebraMap R (CartierDual R B)))

include hker in

theorem eq_of_isIdempotentElem_of_apply_eq {e e' : CartierDual R B} (he : IsIdempotentElem e)
    (he' : IsIdempotentElem e') (h : r e = r e') : e = e' := by
  obtain ⟨e₀, -, huniq⟩ := HenselianLocalRing.existsUnique_isIdempotentElem_mk_eq_of_moduleFinite
    (R := R) (S := CartierDual R B)
    (Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R (CartierDual R B))) e)
    (he.map (Ideal.Quotient.mk _))
  have hmk : Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R (CartierDual R B))) e' =
      Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R (CartierDual R B))) e := by
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← hker, RingHom.mem_ker, map_sub, h, sub_self]
  exact (huniq e ⟨he, rfl⟩).trans (huniq e' ⟨he', hmk⟩).symm

include hsurj hker in

theorem exists_isIdempotentElem_apply_eq (t : CartierDual (ResidueField R) (ResidueField R ⊗[R] B))
    (ht : IsIdempotentElem t) : ∃ e : CartierDual R B, IsIdempotentElem e ∧ r e = t := by
  obtain ⟨s, rfl⟩ := hsurj t
  have hs : IsIdempotentElem (Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R (CartierDual R B))) s) := by
    change Ideal.Quotient.mk _ s * Ideal.Quotient.mk _ s = Ideal.Quotient.mk _ s
    rw [← map_mul, Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← hker, RingHom.mem_ker, map_sub, map_mul, ht.eq, sub_self]
  obtain ⟨e, ⟨he, hmk⟩, -⟩ := HenselianLocalRing.existsUnique_isIdempotentElem_mk_eq_of_moduleFinite
    (R := R) (S := CartierDual R B) _ hs
  refine ⟨e, he, ?_⟩
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← hker, RingHom.mem_ker, map_sub, sub_eq_zero] at hmk
  exact hmk

include hsurj hker in

theorem exists_lift_family {M : Type w} [Fintype M]
    (ē : M → CartierDual (ResidueField R) (ResidueField R ⊗[R] B))
    (hidem : ∀ m, IsIdempotentElem (ē m)) (horth : ∀ a b, a ≠ b → ē a * ē b = 0) (hsum : ∑ m, ē m = 1) :
    ∃ e : M → CartierDual R B,
      (∀ m, IsIdempotentElem (e m)) ∧ (∀ a b, a ≠ b → e a * e b = 0) ∧ ∑ m, e m = 1 ∧ ∀ m, r (e m) = ē m := by
  choose e he hre using fun m => exists_isIdempotentElem_apply_eq r hsurj hker (ē m) (hidem m)
  have horth' : ∀ a b, a ≠ b → e a * e b = 0 := by
    intro a b hab
    refine eq_of_isIdempotentElem_of_apply_eq r hker ((he a).mul (he b)) IsIdempotentElem.zero ?_
    rw [map_mul, hre, hre, horth a b hab, map_zero]
  have hOI : OrthogonalIdempotents e := ⟨he, fun a b hab => horth' a b hab⟩
  refine ⟨e, he, horth', ?_, hre⟩
  refine eq_of_isIdempotentElem_of_apply_eq r hker hOI.isIdempotentElem_sum IsIdempotentElem.one ?_
  rw [map_sum, map_one]
  simp_rw [hre]
  exact hsum

end Lift

end CoalgLiftHensel

open CoalgLiftHensel in
theorem solution
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {B : Type v} [CommRing B] [HopfAlgebra R B] [Module.Finite R B] [Module.Free R B] [Coalgebra.IsCocomm R B]
    (M : Type w) [AddCommGroup M] [Finite M]
    (f₀ : ResidueField R ⊗[R] B →ₗc[ResidueField R] AddMonoidAlgebra (ResidueField R) M) :
    ∃ f : B →ₗc[R] AddMonoidAlgebra R M,
      (AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R (ResidueField R))).toLinearMap ∘ₗ f.toLinearMap =
        (f₀.toLinearMap.restrictScalars R) ∘ₗ
          (Algebra.TensorProduct.includeRight (R := R) (A := ResidueField R) (B := B)).toLinearMap := by
  classical
  haveI : Fintype M := Fintype.ofFinite M

  obtain ⟨ē, hidem, horth, hsum, hf₀⟩ :=
    CartierDual.exists_isIdempotentElem_eq_sum_single_of_coalgHom_addMonoidAlgebra
      (S := ResidueField R) (B := ResidueField R ⊗[R] B) M f₀

  obtain ⟨r, hr, hsurj, hker⟩ :=
    CartierDual.exists_ringHom_apply_eq_dualBaseChangeLin_tmul_of_isLocalRing (R := R) (B := B)

  obtain ⟨e, he, horth', hsum', hre⟩ := exists_lift_family r hsurj hker ē hidem horth hsum

  obtain ⟨f, hf⟩ :=
    CartierDual.exists_coalgHom_addMonoidAlgebra_eq_sum_single_of_isIdempotentElem (S := R) (B := B) M e he horth' hsum'
  refine ⟨f, LinearMap.ext fun b => ?_⟩
  change AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R (ResidueField R)) (f b) =
    f₀ (Algebra.TensorProduct.includeRight (R := R) (A := ResidueField R) (B := B) b)
  rw [hf, hf₀, map_sum, Algebra.TensorProduct.includeRight_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [AddMonoidAlgebra.mapAlgHom_single, ← hre, hr, CartierDual.dualBaseChangeLin_tmul_tmul, one_mul, one_mul]
  rfl

end S_CoalgHom_exists_addMonoidAlgebra_lift_residueField_of_henselianLocalRing
end P2MW
export P2MW.S_CoalgHom_exists_addMonoidAlgebra_lift_residueField_of_henselianLocalRing (solution)
