-- Prove2me | solution 1 for Deformation.DieudonneModule.exists_finrank_eq_pow_and_natCard_le_pow_of_isLocalRing_cartierDual
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/035a5bf2-e8d5-52d5-bdda-e42f372f4600

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_ModpRealization
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Theorems.Thm_Deformation_DieudonneModule_exists_surjective_of
import Theorems.Thm_Deformation_DieudonneModule_exact_map_hopfKerVal_map
import Theorems.Thm_HopfAlgebra_exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective
import Theorems.Thm_HopfAlgebra_finrank_eq_pow_finrank_primitives_of_forall_convPow_prime_eq_zero
import Theorems.Thm_Deformation_mem_wittHom_one_iff_coeff_mem_primitives
import Theorems.Thm_Deformation_wittHomShift_surjective_of_forall_convPow_eq_zero
import Theorems.Thm_HopfAlgebra_exists_ne_zero_comul_eq_tmul_one_add_one_tmul_of_isLocalRing_cartierDual
import Theorems.Thm_HopfAlgebra_isLocalRing_cartierDual_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_DieudonneModule_exists_finrank_eq_pow_and_natCard_le_pow_of_isLocalRing_cartierDual
p2m_attr_erase "instance" "CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra"

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

universe u v w

section InlinedHopfIdealQuotient
open Coalgebra Bialgebra

section IsHopfIdeal'

variable (R : Type*) [CommRing R] {H : Type*} [CommRing H] [HopfAlgebra R H]

namespace Ideal p2m_export "Ideal" "height Quotient.eq_zero_iff_mem Quotient.mkₐ Quotient.liftₐ quotientKerEquivRange mem_bot span isPrime_bot Quotient.algHom_ext Quotient.mk map ext mem_span_singleton' Quotient.liftₐ_comp Quotient.mkₐ_eq_mk subset_span Quotient.mk_surjective" end Ideal
namespace Ideal
p2m_open_scoped "Ideal" in

private class _root_.Ideal.IsHopfIdeal' (I : Ideal H) : Prop where
  map_mkₐ_comul_eq_zero : ∀ x ∈ I,
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)
      (Coalgebra.comul (R := R) x) = 0
  counit_eq_zero : ∀ x ∈ I, Coalgebra.counit (R := R) x = 0
  antipode_mem : ∀ x ∈ I, HopfAlgebra.antipode R x ∈ I

end Ideal
p2m_export "" "Ideal.IsHopfIdeal'"
p2m_export_all "" "Ideal.IsHopfIdeal'"
p2m_open_scoped "Ideal" in
scoped instance Ideal.isHopfIdeal_bot : (⊥ : Ideal H).IsHopfIdeal' R where
  map_mkₐ_comul_eq_zero x hx := by rw [(Ideal.mem_bot).1 hx]; simp
  counit_eq_zero x hx := by rw [(Ideal.mem_bot).1 hx]; simp
  antipode_mem x hx := by rw [(Ideal.mem_bot).1 hx]; simp

p2m_reactivate "P2MW.S_Deformation_DieudonneModule_exists_finrank_eq_pow_and_natCard_le_pow_of_isLocalRing_cartierDual.Ideal"
end IsHopfIdeal'
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_exists_finrank_eq_pow_and_natCard_le_pow_of_isLocalRing_cartierDual.Ideal"

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk antipode_one ofAlgHom mul_antipode_lTensor_comul_apply antipode_mul mul_antipode_rTensor_comul mul_antipode_lTensor_comul mul_antipode_rTensor_comul_apply hopfKer exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective finrank_eq_pow_finrank_primitives_of_forall_convPow_prime_eq_zero exists_ne_zero_comul_eq_tmul_one_add_one_tmul_of_isLocalRing_cartierDual isLocalRing_cartierDual_of_surjective"
p2m_open "HopfAlgebra"

namespace HopfIdealQuotient

variable (R : Type*) [CommRing R] {H : Type*} [CommRing H] [HopfAlgebra R H]
variable (I : Ideal H) [hI : I.IsHopfIdeal' R]

private def _root_.HopfAlgebra.HopfIdealQuotient.comul : H ⧸ I →ₐ[R] (H ⧸ I) ⊗[R] (H ⧸ I) :=
  Ideal.Quotient.liftₐ I
    ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)).comp
      (comulAlgHom R H))
    (fun x hx => hI.map_mkₐ_comul_eq_zero x hx)

p2m_export "HopfAlgebra.HopfIdealQuotient" "comul"
theorem comul_comp_mkₐ :
    (comul R I).comp (Ideal.Quotient.mkₐ R I) =
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)).comp
        (comulAlgHom R H) :=
  Ideal.Quotient.liftₐ_comp _ _ _

@[scoped simp] theorem comul_mk (x : H) :
    comul R I (Ideal.Quotient.mk I x) =
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)
        (Coalgebra.comul (R := R) x) := rfl

private def _root_.HopfAlgebra.HopfIdealQuotient.counit : H ⧸ I →ₐ[R] R :=
  Ideal.Quotient.liftₐ I (counitAlgHom R H) (fun x hx => hI.counit_eq_zero x hx)

p2m_export "HopfAlgebra.HopfIdealQuotient" "counit"
theorem counit_comp_mkₐ : (counit R I).comp (Ideal.Quotient.mkₐ R I) = counitAlgHom R H :=
  Ideal.Quotient.liftₐ_comp _ _ _

@[scoped simp] theorem counit_mk (x : H) :
    counit R I (Ideal.Quotient.mk I x) = Coalgebra.counit (R := R) x := rfl

private theorem map_apply_eq_linearMap {A B C D : Type*} [CommRing A] [CommRing B]
    [CommRing C] [CommRing D] [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    (f : A →ₐ[R] C) (g : B →ₐ[R] D) (z : A ⊗[R] B) :
    Algebra.TensorProduct.map f g z = TensorProduct.map f.toLinearMap g.toLinearMap z := rfl

private theorem _root_.HopfAlgebra.HopfIdealQuotient.rTensor_counit_comul :
    (Algebra.TensorProduct.map (counit R I) (.id R (H ⧸ I))).comp (comul R I) =
      (Algebra.TensorProduct.lid R (H ⧸ I)).symm := by
  refine Ideal.Quotient.algHom_ext R ?_
  rw [AlgHom.comp_assoc, comul_comp_mkₐ, ← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp,
    counit_comp_mkₐ, AlgHom.id_comp]
  refine AlgHom.ext fun x => ?_
  simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom, Algebra.TensorProduct.lid_symm_apply,
    map_apply_eq_linearMap, Bialgebra.comulAlgHom_apply]
  rw [show TensorProduct.map (counitAlgHom R H).toLinearMap (Ideal.Quotient.mkₐ R I).toLinearMap
      = ((Ideal.Quotient.mkₐ R I).toLinearMap.lTensor R) ∘ₗ
          ((counitAlgHom R H).toLinearMap.rTensor H) from
      (LinearMap.lTensor_comp_rTensor _ _ _).symm, LinearMap.comp_apply]
  rw [show ((counitAlgHom R H).toLinearMap.rTensor H) (Coalgebra.comul x) = 1 ⊗ₜ x from
    Coalgebra.rTensor_counit_comul x]
  simp

p2m_export "HopfAlgebra.HopfIdealQuotient" "rTensor_counit_comul"
private theorem _root_.HopfAlgebra.HopfIdealQuotient.lTensor_counit_comul :
    (Algebra.TensorProduct.map (.id R (H ⧸ I)) (counit R I)).comp (comul R I) =
      (Algebra.TensorProduct.rid R R (H ⧸ I)).symm := by
  refine Ideal.Quotient.algHom_ext R ?_
  rw [AlgHom.comp_assoc, comul_comp_mkₐ, ← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp,
    counit_comp_mkₐ, AlgHom.id_comp]
  refine AlgHom.ext fun x => ?_
  simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom, Algebra.TensorProduct.rid_symm_apply,
    map_apply_eq_linearMap, Bialgebra.comulAlgHom_apply]
  rw [show TensorProduct.map (Ideal.Quotient.mkₐ R I).toLinearMap (counitAlgHom R H).toLinearMap
      = ((Ideal.Quotient.mkₐ R I).toLinearMap.rTensor R) ∘ₗ
          ((counitAlgHom R H).toLinearMap.lTensor H) from
      (LinearMap.rTensor_comp_lTensor _ _ _).symm, LinearMap.comp_apply]
  rw [show ((counitAlgHom R H).toLinearMap.lTensor H) (Coalgebra.comul x) = x ⊗ₜ 1 from
    Coalgebra.lTensor_counit_comul x]
  simp

p2m_export "HopfAlgebra.HopfIdealQuotient" "lTensor_counit_comul"

private theorem assoc_map_map_apply {A B : Type*} [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (f : A →ₐ[R] B) (z : (A ⊗[R] A) ⊗[R] A) :
    (Algebra.TensorProduct.assoc R R R B B B)
        (Algebra.TensorProduct.map (Algebra.TensorProduct.map f f) f z) =
      Algebra.TensorProduct.map f (Algebra.TensorProduct.map f f)
        (Algebra.TensorProduct.assoc R R R A A A z) := by
  induction z with
  | zero => simp
  | tmul xy c =>
    induction xy with
    | zero => simp
    | tmul a b => simp
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem coassoc :
    (Algebra.TensorProduct.assoc R R R (H ⧸ I) (H ⧸ I) (H ⧸ I)).toAlgHom.comp
        ((Algebra.TensorProduct.map (comul R I) (.id R (H ⧸ I))).comp (comul R I)) =
      (Algebra.TensorProduct.map (.id R (H ⧸ I)) (comul R I)).comp (comul R I) := by
  refine Ideal.Quotient.algHom_ext R ?_
  refine AlgHom.ext fun x => ?_
  set π := Ideal.Quotient.mkₐ R I

  have hL : ∀ z : H ⊗[R] H,
      Algebra.TensorProduct.map (comul R I) (.id R (H ⧸ I)) (Algebra.TensorProduct.map π π z) =
        Algebra.TensorProduct.map (Algebra.TensorProduct.map π π) π
          (Algebra.TensorProduct.map (comulAlgHom R H) (.id R H) z) := by
    intro z
    induction z with
    | zero => simp
    | tmul a b => simp [π, Ideal.Quotient.mkₐ_eq_mk]
    | add z w hz hw => simp only [map_add, hz, hw]
  have hR : ∀ z : H ⊗[R] H,
      Algebra.TensorProduct.map (.id R (H ⧸ I)) (comul R I) (Algebra.TensorProduct.map π π z) =
        Algebra.TensorProduct.map π (Algebra.TensorProduct.map π π)
          (Algebra.TensorProduct.map (.id R H) (comulAlgHom R H) z) := by
    intro z
    induction z with
    | zero => simp
    | tmul a b => simp [π, Ideal.Quotient.mkₐ_eq_mk]
    | add z w hz hw => simp only [map_add, hz, hw]
  have hx : comul R I (π x) = Algebra.TensorProduct.map π π (comulAlgHom R H x) := by
    simp [π, Ideal.Quotient.mkₐ_eq_mk]
  simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom, hx, hL, hR, assoc_map_map_apply]
  congr 1
  have hassoc : ∀ z : (H ⊗[R] H) ⊗[R] H,
      Algebra.TensorProduct.assoc R R R H H H z = TensorProduct.assoc R H H H z := by
    intro z
    induction z with
    | zero => simp
    | tmul xy c =>
      induction xy with
      | zero => simp
      | tmul a b => simp
      | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [map_apply_eq_linearMap, map_apply_eq_linearMap, hassoc]
  exact Coalgebra.coassoc_apply x

scoped instance instBialgebra : Bialgebra R (H ⧸ I) :=
  Bialgebra.ofAlgHom (comul R I) (counit R I) (coassoc R I) (rTensor_counit_comul R I)
    (lTensor_counit_comul R I)

theorem comulAlgHom_eq : comulAlgHom R (H ⧸ I) = comul R I := rfl

theorem counitAlgHom_eq : counitAlgHom R (H ⧸ I) = counit R I := rfl

theorem coalgebra_comul_mk (x : H) :
    Coalgebra.comul (R := R) (Ideal.Quotient.mk I x) =
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)
        (Coalgebra.comul (R := R) x) := rfl

theorem coalgebra_counit_mk (x : H) :
    Coalgebra.counit (R := R) (Ideal.Quotient.mk I x) = Coalgebra.counit (R := R) x := rfl

def sAlgHom : H →ₐ[R] H :=
  AlgHom.ofLinearMap (HopfAlgebra.antipode R) HopfAlgebra.antipode_one fun a b => by
    rw [HopfAlgebra.antipode_mul, mul_comm]

@[scoped simp] theorem sAlgHom_apply (x : H) : sAlgHom R (H := H) x = HopfAlgebra.antipode R x := rfl

private def _root_.HopfAlgebra.HopfIdealQuotient.antipode : H ⧸ I →ₐ[R] H ⧸ I :=
  Ideal.Quotient.liftₐ I ((Ideal.Quotient.mkₐ R I).comp (sAlgHom R)) (fun x hx => by
    simp only [AlgHom.comp_apply, sAlgHom_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hI.antipode_mem x hx)

p2m_export "HopfAlgebra.HopfIdealQuotient" "antipode"
theorem antipode_comp_mkₐ :
    (antipode R I).comp (Ideal.Quotient.mkₐ R I) = (Ideal.Quotient.mkₐ R I).comp (sAlgHom R) :=
  Ideal.Quotient.liftₐ_comp _ _ _

private theorem lift_antipode_id_comp_map :
    (Algebra.TensorProduct.lift (antipode R I) (.id R (H ⧸ I)) fun _ _ => .all _ _).comp
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)) =
      (Ideal.Quotient.mkₐ R I).comp
        (Algebra.TensorProduct.lift (sAlgHom R) (.id R H) fun _ _ => .all _ _) := by
  ext x
  · simp [Ideal.Quotient.mkₐ_eq_mk, antipode]
  · simp [Ideal.Quotient.mkₐ_eq_mk]

private theorem lift_id_antipode_comp_map :
    (Algebra.TensorProduct.lift (.id R (H ⧸ I)) (antipode R I) fun _ _ => .all _ _).comp
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)) =
      (Ideal.Quotient.mkₐ R I).comp
        (Algebra.TensorProduct.lift (.id R H) (sAlgHom R) fun _ _ => .all _ _) := by
  ext x
  · simp [Ideal.Quotient.mkₐ_eq_mk]
  · simp [Ideal.Quotient.mkₐ_eq_mk, antipode]

private theorem lift_sAlgHom_comp_apply (z : H ⊗[R] H) :
    Algebra.TensorProduct.lift (sAlgHom R) (.id R H) (fun _ _ => .all _ _) z =
      LinearMap.mul' R H ((HopfAlgebra.antipode R).rTensor H z) := by
  induction z with
  | zero => simp
  | tmul x y => simp [LinearMap.rTensor_tmul]
  | add x y hx hy => simp [map_add, hx, hy]

private theorem lift_id_sAlgHom_apply (z : H ⊗[R] H) :
    Algebra.TensorProduct.lift (.id R H) (sAlgHom R) (fun _ _ => .all _ _) z =
      LinearMap.mul' R H ((HopfAlgebra.antipode R).lTensor H z) := by
  induction z with
  | zero => simp
  | tmul x y => simp [LinearMap.lTensor_tmul]
  | add x y hx hy => simp [map_add, hx, hy]

private theorem lift_sAlgHom_id_comp_comulAlgHom :
    (Algebra.TensorProduct.lift (sAlgHom R) (.id R H) fun _ _ => .all _ _).comp
        (comulAlgHom R H) = (Algebra.ofId R H).comp (counitAlgHom R H) := by
  refine AlgHom.ext fun x => ?_
  rw [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, lift_sAlgHom_comp_apply,
    HopfAlgebra.mul_antipode_rTensor_comul_apply]
  simp [Algebra.ofId_apply]

private theorem lift_id_sAlgHom_comp_comulAlgHom :
    (Algebra.TensorProduct.lift (.id R H) (sAlgHom R) fun _ _ => .all _ _).comp
        (comulAlgHom R H) = (Algebra.ofId R H).comp (counitAlgHom R H) := by
  refine AlgHom.ext fun x => ?_
  rw [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, lift_id_sAlgHom_apply,
    HopfAlgebra.mul_antipode_lTensor_comul_apply]
  simp [Algebra.ofId_apply]

theorem mul_antipode_rTensor_comul :
    (Algebra.TensorProduct.lift (antipode R I) (.id R (H ⧸ I)) fun _ _ => .all _ _).comp
        (comulAlgHom R (H ⧸ I)) =
      (Algebra.ofId R (H ⧸ I)).comp (counitAlgHom R (H ⧸ I)) := by
  refine Ideal.Quotient.algHom_ext R ?_
  rw [comulAlgHom_eq, counitAlgHom_eq, AlgHom.comp_assoc, comul_comp_mkₐ, ← AlgHom.comp_assoc,
    lift_antipode_id_comp_map, AlgHom.comp_assoc, lift_sAlgHom_id_comp_comulAlgHom,
    AlgHom.comp_assoc, counit_comp_mkₐ, ← AlgHom.comp_assoc]
  congr 1

theorem mul_antipode_lTensor_comul :
    (Algebra.TensorProduct.lift (.id R (H ⧸ I)) (antipode R I) fun _ _ => .all _ _).comp
        (comulAlgHom R (H ⧸ I)) =
      (Algebra.ofId R (H ⧸ I)).comp (counitAlgHom R (H ⧸ I)) := by
  refine Ideal.Quotient.algHom_ext R ?_
  rw [comulAlgHom_eq, counitAlgHom_eq, AlgHom.comp_assoc, comul_comp_mkₐ, ← AlgHom.comp_assoc,
    lift_id_antipode_comp_map, AlgHom.comp_assoc, lift_id_sAlgHom_comp_comulAlgHom,
    AlgHom.comp_assoc, counit_comp_mkₐ, ← AlgHom.comp_assoc]
  congr 1

scoped instance instHopfAlgebra : HopfAlgebra R (H ⧸ I) :=
  HopfAlgebra.ofAlgHom (antipode R I) (mul_antipode_rTensor_comul R I)
    (mul_antipode_lTensor_comul R I)

scoped instance instIsCocomm [Coalgebra.IsCocomm R H] : Coalgebra.IsCocomm R (H ⧸ I) where
  comm_comp_comul := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [LinearMap.comp_apply, coalgebra_comul_mk]
    conv_rhs => rw [← Coalgebra.comm_comp_comul R H]
    rw [LinearMap.comp_apply]
    generalize Coalgebra.comul (R := R) x = z
    induction z with
    | zero => simp
    | tmul a b => simp
    | add z w hz hw => simp only [map_add, hz, hw]

def quotientBialgHom : H →ₐc[R] H ⧸ I :=
  BialgHom.ofAlgHom (Ideal.Quotient.mkₐ R I) (counit_comp_mkₐ R I) (comul_comp_mkₐ R I).symm

@[scoped simp] theorem quotientBialgHom_apply (x : H) :
    quotientBialgHom R I x = Ideal.Quotient.mk I x := rfl

theorem quotientBialgHom_surjective : Function.Surjective (quotientBialgHom R I) :=
  Ideal.Quotient.mk_surjective

end HopfIdealQuotient
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_exists_finrank_eq_pow_and_natCard_le_pow_of_isLocalRing_cartierDual.Ideal P2MW.S_Deformation_DieudonneModule_exists_finrank_eq_pow_and_natCard_le_pow_of_isLocalRing_cartierDual.HopfAlgebra.HopfIdealQuotient"

end HopfAlgebra
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_exists_finrank_eq_pow_and_natCard_le_pow_of_isLocalRing_cartierDual.Ideal P2MW.S_Deformation_DieudonneModule_exists_finrank_eq_pow_and_natCard_le_pow_of_isLocalRing_cartierDual.HopfAlgebra.HopfIdealQuotient P2MW.S_Deformation_DieudonneModule_exists_finrank_eq_pow_and_natCard_le_pow_of_isLocalRing_cartierDual.HopfAlgebra"

end InlinedHopfIdealQuotient
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_exists_finrank_eq_pow_and_natCard_le_pow_of_isLocalRing_cartierDual.Ideal P2MW.S_Deformation_DieudonneModule_exists_finrank_eq_pow_and_natCard_le_pow_of_isLocalRing_cartierDual.HopfAlgebra.HopfIdealQuotient P2MW.S_Deformation_DieudonneModule_exists_finrank_eq_pow_and_natCard_le_pow_of_isLocalRing_cartierDual.HopfAlgebra"

namespace DieudonneUpper

open Coalgebra Bialgebra Function Deformation Deformation.DieudonneModule

section Primitive

variable {k : Type u} [Field k] {B : Type v} [CommRing B] [HopfAlgebra k B]

theorem counit_eq_zero_of_primitive {a : B} (ha : comul (R := k) a = a ⊗ₜ[k] 1 + 1 ⊗ₜ[k] a) :
    counit (R := k) a = 0 := by
  have h := Coalgebra.rTensor_counit_comul (R := k) a
  rw [ha, map_add, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, counit_one] at h

  have h2 : (counit (R := k) a) ⊗ₜ[k] (1 : B) = 0 := by
    have := congrArg (fun t => t - (1 : k) ⊗ₜ[k] a) h
    simpa using this
  have h3 := congrArg (TensorProduct.lid k B) h2
  rw [TensorProduct.lid_tmul, map_zero, smul_eq_zero] at h3
  rcases h3 with h3 | h3
  · exact h3
  · have : a = 0 := by rw [← mul_one a, h3, mul_zero]
    rw [this, map_zero]

theorem antipode_eq_neg_of_primitive {a : B} (ha : comul (R := k) a = a ⊗ₜ[k] 1 + 1 ⊗ₜ[k] a) :
    HopfAlgebra.antipode k a = -a := by
  have h := HopfAlgebra.mul_antipode_rTensor_comul_apply (R := k) a
  rw [ha, map_add, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, map_add, LinearMap.mul'_apply,
    LinearMap.mul'_apply, HopfAlgebra.antipode_one, one_mul, mul_one,
    counit_eq_zero_of_primitive ha, map_zero] at h
  exact eq_neg_of_add_eq_zero_left h

theorem isHopfIdeal_span_primitive {a : B} (ha : comul (R := k) a = a ⊗ₜ[k] 1 + 1 ⊗ₜ[k] a) :
    (Ideal.span {a}).IsHopfIdeal' k where
  map_mkₐ_comul_eq_zero x hx := by
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    have hπa : Ideal.Quotient.mkₐ k (Ideal.span {a}) a = 0 := by
      rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span rfl
    rw [← Bialgebra.comulAlgHom_apply, map_mul, map_mul, Bialgebra.comulAlgHom_apply,
      Bialgebra.comulAlgHom_apply, ha, map_add, Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.map_tmul, hπa]
    simp
  counit_eq_zero x hx := by
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [counit_mul, counit_eq_zero_of_primitive ha, mul_zero]
  antipode_mem x hx := by
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [HopfAlgebra.antipode_mul, antipode_eq_neg_of_primitive ha]
    exact Ideal.mem_span_singleton'.2 ⟨-HopfAlgebra.antipode k y, by ring⟩

end Primitive
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_exists_finrank_eq_pow_and_natCard_le_pow_of_isLocalRing_cartierDual.Ideal P2MW.S_Deformation_DieudonneModule_exists_finrank_eq_pow_and_natCard_le_pow_of_isLocalRing_cartierDual.HopfAlgebra.HopfIdealQuotient P2MW.S_Deformation_DieudonneModule_exists_finrank_eq_pow_and_natCard_le_pow_of_isLocalRing_cartierDual.HopfAlgebra"

section Derivation

variable {k : Type u} [Field k] {B : Type v} [CommRing B] [Bialgebra k B]

def dmul (a : B) (β : WithConv (B →ₗ[k] k)) : WithConv (B →ₗ[k] k) :=
  WithConv.toConv (β.ofConv ∘ₗ LinearMap.mulLeft k a)

@[scoped simp] theorem dmul_apply (a : B) (β : WithConv (B →ₗ[k] k)) (x : B) : dmul a β x = β (a * x) := rfl

theorem dmul_add (a : B) (β γ : WithConv (B →ₗ[k] k)) : dmul a (β + γ) = dmul a β + dmul a γ := rfl

private theorem mul'_map_aone_mul (β γ : WithConv (B →ₗ[k] k)) (a : B) (z : B ⊗[k] B) :
    LinearMap.mul' k k (TensorProduct.map β.ofConv γ.ofConv ((a ⊗ₜ[k] (1 : B)) * z)) =
      LinearMap.mul' k k (TensorProduct.map (dmul a β).ofConv γ.ofConv z) := by
  induction z with
  | zero => simp
  | tmul x y => simp [Algebra.TensorProduct.tmul_mul_tmul, dmul]
  | add x y hx hy => simp only [mul_add, map_add, hx, hy]

private theorem mul'_map_onea_mul (β γ : WithConv (B →ₗ[k] k)) (a : B) (z : B ⊗[k] B) :
    LinearMap.mul' k k (TensorProduct.map β.ofConv γ.ofConv (((1 : B) ⊗ₜ[k] a) * z)) =
      LinearMap.mul' k k (TensorProduct.map β.ofConv (dmul a γ).ofConv z) := by
  induction z with
  | zero => simp
  | tmul x y => simp [Algebra.TensorProduct.tmul_mul_tmul, dmul]
  | add x y hx hy => simp only [mul_add, map_add, hx, hy]

theorem dmul_mul {a : B} (ha : comul (R := k) a = a ⊗ₜ[k] 1 + 1 ⊗ₜ[k] a)
    (β γ : WithConv (B →ₗ[k] k)) : dmul a (β * γ) = dmul a β * γ + β * dmul a γ := by
  apply WithConv.ext
  refine LinearMap.ext fun x => ?_
  change (β * γ) (a * x) = (dmul a β * γ) x + (β * dmul a γ) x
  rw [LinearMap.convMul_apply, LinearMap.convMul_apply, LinearMap.convMul_apply]
  have hΔ : comul (R := k) (a * x) = (a ⊗ₜ[k] (1 : B) + (1 : B) ⊗ₜ[k] a) * comul (R := k) x := by
    rw [← Bialgebra.comulAlgHom_apply, map_mul, Bialgebra.comulAlgHom_apply,
      Bialgebra.comulAlgHom_apply, ha]
  rw [hΔ, add_mul, map_add, map_add, mul'_map_aone_mul, mul'_map_onea_mul]

theorem dmul_pow {a : B} (ha : comul (R := k) a = a ⊗ₜ[k] 1 + 1 ⊗ₜ[k] a) [Coalgebra.IsCocomm k B]
    (β : WithConv (B →ₗ[k] k)) : ∀ n : ℕ, dmul a (β ^ (n + 1)) = (n + 1) • (β ^ n * dmul a β)
  | 0 => by rw [zero_add, pow_one, pow_zero, one_mul, one_smul]
  | n + 1 => by
    rw [pow_succ, dmul_mul ha, dmul_pow ha β n, smul_mul_assoc, mul_right_comm, ← pow_succ]
    simp only [add_nsmul, one_nsmul]

theorem convPow_apply_one (β : WithConv (B →ₗ[k] k)) : ∀ n : ℕ, (β ^ n) 1 = (β 1) ^ n
  | 0 => by rw [pow_zero, pow_zero, LinearMap.convOne_apply, counit_one]; simp
  | n + 1 => by
    rw [pow_succ, pow_succ, LinearMap.convMul_apply, comul_one, Algebra.TensorProduct.one_def,
      TensorProduct.map_tmul, LinearMap.mul'_apply, convPow_apply_one β n]

theorem add_apply' (f g : WithConv (B →ₗ[k] k)) (z : B) : (f + g) z = f z + g z := rfl

theorem nsmul_apply' (n : ℕ) (f : WithConv (B →ₗ[k] k)) (z : B) : (n • f) z = n • f z := by
  induction n with
  | zero => rw [zero_smul, zero_smul]; rfl
  | succ n ih => rw [succ_nsmul, succ_nsmul, add_apply', ih]

theorem convPow_prime_eq_zero (p : ℕ) [Fact p.Prime] [CharP k p] [Coalgebra.IsCocomm k B] {a : B}
    (ha : comul (R := k) a = a ⊗ₜ[k] 1 + 1 ⊗ₜ[k] a)
    (hgen : ∀ x : B, counit (R := k) x = 0 → x ∈ Ideal.span {a})
    (β : WithConv (B →ₗ[k] k)) (hβ : β.ofConv 1 = 0) : β ^ p = 0 := by
  apply WithConv.ext
  refine LinearMap.ext fun x => ?_
  change (β ^ p) x = 0

  have hx : x - counit (R := k) x • (1 : B) ∈ Ideal.span {a} :=
    hgen _ (by rw [map_sub, map_smul, counit_one, smul_eq_mul, mul_one, sub_self])
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hx
  have hx' : x = counit (R := k) x • (1 : B) + a * y := by rw [mul_comm, hy, add_sub_cancel]
  rw [hx', map_add, map_smul, convPow_apply_one]
  have hp1 : (β ^ p) (a * y) = 0 := by
    have := dmul_pow ha β (p - 1)
    rw [Nat.sub_add_cancel (Fact.out : p.Prime).one_le] at this
    have h2 : (dmul a (β ^ p)) y = 0 := by
      rw [this, nsmul_apply', nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
    exact h2
  rw [hp1, add_zero]
  change counit (R := k) x • (β.ofConv 1) ^ p = 0
  rw [hβ, zero_pow (Fact.out : p.Prime).ne_zero, smul_zero]

end Derivation
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_exists_finrank_eq_pow_and_natCard_le_pow_of_isLocalRing_cartierDual.Ideal P2MW.S_Deformation_DieudonneModule_exists_finrank_eq_pow_and_natCard_le_pow_of_isLocalRing_cartierDual.HopfAlgebra.HopfIdealQuotient P2MW.S_Deformation_DieudonneModule_exists_finrank_eq_pow_and_natCard_le_pow_of_isLocalRing_cartierDual.HopfAlgebra"

section MTools

variable {k : Type u} [Field k] {p : ℕ} [hp : Fact p.Prime]
variable {C : Type v} [CommRing C] [Bialgebra k C]

theorem of_one_surjective (h : ∀ m : ℕ, 1 ≤ m → Surjective (wittHomShift k p m C)) :
    Surjective (of k p C 1) := by
  intro z
  obtain ⟨n, x, rfl⟩ := exists_of z
  induction n with
  | zero =>

    refine ⟨wittHomShift k p 0 C x, ?_⟩
    rw [of_shift]
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨x, rfl⟩
    · obtain ⟨y, rfl⟩ := h n hn x
      rw [of_shift]
      exact ih y

theorem natCard_wittHom_one_eq [CharP k p] {B : Type v} [CommRing B] [HopfAlgebra k B] :
    Nat.card (wittHom k p 1 B) = Nat.card (primitives k B) := by
  refine Nat.card_eq_of_bijective (fun x => ⟨(x : TruncatedWittVector p 1 B).coeff 0,
    (Deformation.mem_wittHom_one_iff_coeff_mem_primitives k p B x).1 x.2⟩) ⟨?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    refine TruncatedWittVector.ext fun i => ?_
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact congrArg Subtype.val hxy
  · rintro ⟨b, hb⟩
    refine ⟨⟨TruncatedWittVector.mk p fun _ => b, (Deformation.mem_wittHom_one_iff_coeff_mem_primitives
      k p B _).2 (by simpa using hb)⟩, Subtype.ext (by simp)⟩

theorem natCard_eq_card_ker_mul_card_range {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (f : X →+ Y) : Nat.card X = Nat.card f.ker * Nat.card f.range := by
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker, mul_comm,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv, mul_comm]

end MTools
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_exists_finrank_eq_pow_and_natCard_le_pow_of_isLocalRing_cartierDual.Ideal P2MW.S_Deformation_DieudonneModule_exists_finrank_eq_pow_and_natCard_le_pow_of_isLocalRing_cartierDual.HopfAlgebra.HopfIdealQuotient P2MW.S_Deformation_DieudonneModule_exists_finrank_eq_pow_and_natCard_le_pow_of_isLocalRing_cartierDual.HopfAlgebra"

section UQuot

variable {k : Type u} [Field k]
variable {B : Type v} [CommRing B] [HopfAlgebra k B] [Coalgebra.IsCocomm k B] [Module.Finite k B]
variable {C : Type w} [CommRing C] [Bialgebra k C] [Coalgebra.IsCocomm k C] [Module.Finite k C]

omit [Coalgebra.IsCocomm k C] [Module.Finite k C] in

theorem nontrivial_cartierDual : Nontrivial (CartierDual k C) :=
  ⟨⟨0, 1, fun h => by
    have := congrArg (fun φ : CartierDual k C => φ 1) h
    simp only [CartierDual.one_apply, Bialgebra.counit_one] at this
    exact zero_ne_one this⟩⟩

theorem isLocalRing_cartierDual_of_injective (ι : C →ₐc[k] B) (hι : Injective ι)
    (hB : IsLocalRing (CartierDual k B)) : IsLocalRing (CartierDual k C) := by
  haveI := hB
  haveI := nontrivial_cartierDual (k := k) (C := C)
  refine IsLocalRing.of_surjective' (CartierDual.mapAlgHom ι).toRingHom fun ψ => ?_

  obtain ⟨φ, hφ⟩ := LinearMap.dualMap_surjective_of_injective (f := (ι : C →ₐ[k] B).toLinearMap) hι
    (CartierDual.toDual k C ψ)
  refine ⟨CartierDual.ofDual k B φ, ?_⟩
  apply (CartierDual.toDual k C).injective
  refine LinearMap.ext fun c => ?_
  rw [← hφ]
  rfl

end UQuot
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_exists_finrank_eq_pow_and_natCard_le_pow_of_isLocalRing_cartierDual.Ideal P2MW.S_Deformation_DieudonneModule_exists_finrank_eq_pow_and_natCard_le_pow_of_isLocalRing_cartierDual.HopfAlgebra.HopfIdealQuotient P2MW.S_Deformation_DieudonneModule_exists_finrank_eq_pow_and_natCard_le_pow_of_isLocalRing_cartierDual.HopfAlgebra"

section Induction

variable (k : Type u) [Field k] [Finite k] (p : ℕ) [hp : Fact p.Prime] [CharP k p]

local notation "M" => DieudonneModule k p

theorem finite_dieudonneModule (B : Type v) [CommRing B] [HopfAlgebra k B] [Coalgebra.IsCocomm k B]
    [Module.Finite k B] : Finite (M B) := by
  obtain ⟨N, hN⟩ := Deformation.DieudonneModule.exists_surjective_of k p B
  haveI : Finite B := Module.finite_of_finite k
  haveI : Finite (TruncatedWittVector p N B) := by unfold TruncatedWittVector; infer_instance
  exact Finite.of_surjective _ hN

omit [Finite k] in

theorem base (B : Type v) [CommRing B] [HopfAlgebra k B] [Coalgebra.IsCocomm k B] [Module.Finite k B]
    (hV : ∀ β : WithConv (B →ₗ[k] k), β.ofConv 1 = 0 → β ^ p = 0) :
    ∃ L : ℕ, Module.finrank k B = p ^ L ∧ Nat.card (M B) ≤ Nat.card k ^ L := by
  refine ⟨Module.finrank k (primitives k B),
    HopfAlgebra.finrank_eq_pow_finrank_primitives_of_forall_convPow_prime_eq_zero k p B hV, le_of_eq ?_⟩
  have hshift : ∀ m : ℕ, 1 ≤ m → Surjective (wittHomShift k p m B) :=
    Deformation.wittHomShift_surjective_of_forall_convPow_eq_zero k p B 1 (by simpa using hV)
  have hof : Bijective (of k p B 1) := ⟨of_injective 1, of_one_surjective hshift⟩
  rw [← Nat.card_eq_of_bijective _ hof, natCard_wittHom_one_eq, Module.natCard_eq_pow_finrank (K := k)]

omit [Finite k] [CharP k p] in

theorem card_of_finrank_eq_one (B : Type v) [CommRing B] [HopfAlgebra k B] [Module.Finite k B]
    (h1 : Module.finrank k B = 1) : Nat.card (M B) = 1 := by

  have hinj : Injective (Bialgebra.counitAlgHom k B).toLinearMap := by
    have hs : Surjective (Bialgebra.counitAlgHom k B).toLinearMap := fun r =>
      ⟨algebraMap k B r, by simp⟩
    haveI : Module.Finite k B := inferInstance
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [h1, Module.finrank_self])).2 hs
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun z w => ?_⟩, ⟨0⟩⟩
  suffices h : ∀ z : M B, z = 0 by rw [h z, h w]
  intro z
  obtain ⟨n, x, rfl⟩ := exists_of z
  have : x = 0 := by
    apply Subtype.ext
    refine TruncatedWittVector.ext fun i => ?_
    rw [ZeroMemClass.coe_zero, TruncatedWittVector.coeff_zero]
    apply hinj
    rw [map_zero]
    exact counit_coeff_of_mem_wittHom x.2 i
  rw [this, map_zero]

theorem main : ∀ (n : ℕ) (B : Type v) [CommRing B] [HopfAlgebra k B] [Coalgebra.IsCocomm k B]
    [Module.Finite k B], Module.finrank k B = n → IsLocalRing (CartierDual k B) →
    ∃ L : ℕ, Module.finrank k B = p ^ L ∧ Nat.card (M B) ≤ Nat.card k ^ L := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro B _ _ _ _ hn hB
  by_cases h1 : Module.finrank k B = 1
  · exact ⟨0, by rw [h1, pow_zero], by rw [card_of_finrank_eq_one k p B h1, pow_zero]⟩

  obtain ⟨a, ha0, ha⟩ :=
    HopfAlgebra.exists_ne_zero_comul_eq_tmul_one_add_one_tmul_of_isLocalRing_cartierDual k B hB h1
  by_cases hgen : ∀ x : B, counit (R := k) x = 0 → x ∈ Ideal.span {a}
  ·
    exact base k p B (convPow_prime_eq_zero p ha hgen)
  ·
    push Not at hgen
    obtain ⟨x₀, hx₀ε, hx₀⟩ := hgen
    haveI hI : (Ideal.span {a}).IsHopfIdeal' k := isHopfIdeal_span_primitive ha
    set I : Ideal B := Ideal.span {a} with hIdef
    let π : B →ₐc[k] (B ⧸ I) := HopfAlgebra.HopfIdealQuotient.quotientBialgHom k I
    have hπ : Surjective π := Ideal.Quotient.mk_surjective

    have hQ : IsLocalRing (CartierDual k (B ⧸ I)) :=
      HopfAlgebra.isLocalRing_cartierDual_of_surjective k B (B ⧸ I) π hπ hB
    let Csub := HopfAlgebra.hopfKer π
    have hCsub : IsLocalRing (CartierDual k ↥Csub) :=
      isLocalRing_cartierDual_of_injective (HopfAlgebra.hopfKerVal π)
        (HopfAlgebra.hopfKerVal_injective π) hB

    obtain ⟨-, -, -, hrank⟩ :=
      HopfAlgebra.exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective π hπ
    have hdim : Module.finrank k ↥Csub * Module.finrank k (B ⧸ I) = Module.finrank k B := by
      have := hrank ⟨⊥, Ideal.isPrime_bot⟩
      rwa [Module.rankAtStalk_eq_finrank_of_free] at this
    have hQlt : Module.finrank k (B ⧸ I) < Module.finrank k B := by
      have hle : Module.finrank k (B ⧸ I) ≤ Module.finrank k B :=
        LinearMap.finrank_le_finrank_of_surjective (f := (π : B →ₐ[k] (B ⧸ I)).toLinearMap) hπ
      refine lt_of_le_of_ne hle fun heq => ha0 ?_
      have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq.symm
        (f := (π : B →ₐ[k] (B ⧸ I)).toLinearMap)).2 hπ
      apply hinj
      change Ideal.Quotient.mk I a = Ideal.Quotient.mk I 0
      rw [map_zero, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span rfl
    have hQ2 : 2 ≤ Module.finrank k (B ⧸ I) := by

      by_contra hlt
      push Not at hlt
      have hQpos : 0 < Module.finrank k (B ⧸ I) := by
        rw [Module.finrank_pos_iff]
        exact ⟨⟨0, 1, fun h => by
          have := congrArg (Coalgebra.counit (R := k) (A := (B ⧸ I))) h
          rw [Bialgebra.counit_one, map_zero] at this
          exact zero_ne_one this⟩⟩
      have hQ1 : Module.finrank k (B ⧸ I) = 1 := by omega

      have hs : Surjective (Bialgebra.counitAlgHom k (B ⧸ I)).toLinearMap := fun r =>
        ⟨algebraMap k (B ⧸ I) r, by simp⟩
      have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (by rw [hQ1, Module.finrank_self]) (f := (Bialgebra.counitAlgHom k (B ⧸ I)).toLinearMap)).2 hs
      apply hx₀
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      apply hinj
      change Coalgebra.counit (R := k) (Ideal.Quotient.mk I x₀) = Coalgebra.counit (R := k) (0 : (B ⧸ I))
      rw [map_zero, HopfAlgebra.HopfIdealQuotient.coalgebra_counit_mk, hx₀ε]
    have hClt : Module.finrank k ↥Csub < Module.finrank k B := by
      have hCpos : 0 < Module.finrank k ↥Csub := by
        rw [Module.finrank_pos_iff]
        exact ⟨⟨0, 1, fun h => by
          have h' := congrArg (fun c : ↥Csub => Coalgebra.counit (R := k) (c : B)) h
          simp at h'⟩⟩
      nlinarith

    obtain ⟨LC, hLC, hMC⟩ := ih _ (hn ▸ hClt) ↥Csub rfl hCsub
    obtain ⟨LQ, hLQ, hMQ⟩ := ih _ (hn ▸ hQlt) (B ⧸ I) rfl hQ
    refine ⟨LC + LQ, by rw [pow_add, ← hLC, ← hLQ, hdim], ?_⟩

    haveI := finite_dieudonneModule k p ↥Csub
    haveI := finite_dieudonneModule k p (B ⧸ I)
    haveI := finite_dieudonneModule k p B
    have hexact := Deformation.DieudonneModule.exact_map_hopfKerVal_map k p π
    rw [natCard_eq_card_ker_mul_card_range (DieudonneModule.map k p π), pow_add]
    refine Nat.mul_le_mul (le_trans ?_ hMC) (le_trans ?_ hMQ)
    ·
      have : (DieudonneModule.map k p π).ker ≤ (DieudonneModule.map k p (HopfAlgebra.hopfKerVal π)).range := by
        intro z hz
        exact (hexact z).1 hz
      calc Nat.card (DieudonneModule.map k p π).ker
          ≤ Nat.card (DieudonneModule.map k p (HopfAlgebra.hopfKerVal π)).range :=
            AddSubgroup.card_le_of_le this
        _ ≤ Nat.card (M ↥Csub) :=
            Nat.card_le_card_of_surjective _ (AddMonoidHom.rangeRestrict_surjective _)
    · exact Nat.card_le_card_of_injective _ Subtype.val_injective

end Induction
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_exists_finrank_eq_pow_and_natCard_le_pow_of_isLocalRing_cartierDual.Ideal P2MW.S_Deformation_DieudonneModule_exists_finrank_eq_pow_and_natCard_le_pow_of_isLocalRing_cartierDual.HopfAlgebra.HopfIdealQuotient P2MW.S_Deformation_DieudonneModule_exists_finrank_eq_pow_and_natCard_le_pow_of_isLocalRing_cartierDual.HopfAlgebra"

end DieudonneUpper
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_exists_finrank_eq_pow_and_natCard_le_pow_of_isLocalRing_cartierDual.Ideal P2MW.S_Deformation_DieudonneModule_exists_finrank_eq_pow_and_natCard_le_pow_of_isLocalRing_cartierDual.HopfAlgebra.HopfIdealQuotient P2MW.S_Deformation_DieudonneModule_exists_finrank_eq_pow_and_natCard_le_pow_of_isLocalRing_cartierDual.HopfAlgebra P2MW.S_Deformation_DieudonneModule_exists_finrank_eq_pow_and_natCard_le_pow_of_isLocalRing_cartierDual.DieudonneUpper"

open DieudonneUpper in
theorem solution
    (k : Type u) [Field k] [Finite k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (B : Type v) [CommRing B] [HopfAlgebra k B] [Coalgebra.IsCocomm k B] [Module.Finite k B]
    (hB : IsLocalRing (CartierDual k B)) :
    ∃ L : ℕ, Module.finrank k B = p ^ L ∧
      Nat.card (Deformation.DieudonneModule k p B) ≤ Nat.card k ^ L :=
  main k p _ B rfl hB

end
end S_Deformation_DieudonneModule_exists_finrank_eq_pow_and_natCard_le_pow_of_isLocalRing_cartierDual
end P2MW
export P2MW.S_Deformation_DieudonneModule_exists_finrank_eq_pow_and_natCard_le_pow_of_isLocalRing_cartierDual (solution)
