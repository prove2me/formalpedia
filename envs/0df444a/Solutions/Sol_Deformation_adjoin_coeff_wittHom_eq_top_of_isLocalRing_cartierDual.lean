-- Prove2me | solution 1 for Deformation.adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/e631154d-2458-5f4b-91d2-e1b8999ae617

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_ModpRealization
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Definitions.Def_HopfAlgebra_HopfTower
import Theorems.Thm_HopfAlgebra_wittHomMap_surjective_of_surjective_of_forall_convPow_eq_zero
import Theorems.Thm_Deformation_mem_wittHom_one_iff_coeff_mem_primitives
import Theorems.Thm_HopfAlgebra_exists_ne_zero_comul_eq_tmul_one_add_one_tmul_of_isLocalRing_cartierDual
import Theorems.Thm_HopfAlgebra_isLocalRing_cartierDual_of_surjective
import Theorems.Thm_HopfAlgebra_faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual
p2m_attr_erase "instance" "CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra"
p2m_attr_erase "simp" "CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply"

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

universe u v w

section InlinedHopfIdealQuotient
open Coalgebra Bialgebra

section IsHopfIdeal'

variable (R : Type*) [CommRing R] {H : Type*} [CommRing H] [HopfAlgebra R H]

namespace Ideal p2m_export "Ideal" "map_map Quotient.eq_zero_iff_mem mul_mem_right Quotient.mkₐ Quotient.liftₐ mem_bot span Quotient.mk_algebraMap Quotient.algHom_ext zero_eq_bot Quotient.mk map_id map ext Quotient.liftₐ_comp span_le coe_comap mem_comap pow_mem_pow under comap Quotient.mkₐ_eq_mk subset_span Quotient.mk_surjective" end Ideal
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

p2m_reactivate "P2MW.S_Deformation_adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual.Ideal"
end IsHopfIdeal'
p2m_reactivate "P2MW.S_Deformation_adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual.Ideal"

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk antipode_one ofAlgHom mul_antipode_lTensor_comul_apply antipode_mul mul_antipode_rTensor_comul mul_antipode_lTensor_comul counit_antipode mul_antipode_rTensor_comul_apply sum_counit_right_smul IsHopfSubalgebra IsHopfSubalgebra.range_ι₂ HopfTower.augIdealMap HopfTower.algebraMap_mem_augIdealMap HopfTower.fwdAux HopfTower.fwdAux_apply HopfTower.galoisEquiv HopfTower.galoisEquiv_one_tmul wittHomMap_surjective_of_surjective_of_forall_convPow_eq_zero exists_ne_zero_comul_eq_tmul_one_add_one_tmul_of_isLocalRing_cartierDual isLocalRing_cartierDual_of_surjective faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem"
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
p2m_reactivate "P2MW.S_Deformation_adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual.Ideal P2MW.S_Deformation_adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual.HopfAlgebra.HopfIdealQuotient"

end HopfAlgebra
p2m_reactivate "P2MW.S_Deformation_adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual.Ideal P2MW.S_Deformation_adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual.HopfAlgebra.HopfIdealQuotient P2MW.S_Deformation_adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual.HopfAlgebra"

end InlinedHopfIdealQuotient
p2m_reactivate "P2MW.S_Deformation_adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual.Ideal P2MW.S_Deformation_adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual.HopfAlgebra.HopfIdealQuotient P2MW.S_Deformation_adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual.HopfAlgebra"

namespace DieudonneEmb

open Coalgebra Bialgebra Function Deformation Deformation.DieudonneModule

section WittPoly

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}
variable {k : Type u} [CommRing k] {T : Type v} [CommRing T] [Algebra k T]

omit hp in
theorem coeff_out_mem (S : Subalgebra k T) (x : TruncatedWittVector p n T)
    (hx : ∀ j, x.coeff j ∈ S) (i : ℕ) : x.out.coeff i ∈ S := by
  by_cases hi : i < n
  · have := TruncatedWittVector.coeff_out x ⟨i, hi⟩
    rw [Fin.val_mk] at this
    rw [this]
    exact hx _
  · have : x.out.coeff i = 0 := by
      change (if h : i < n then x.coeff ⟨i, h⟩ else 0) = 0
      rw [dif_neg hi]
    rw [this]
    exact zero_mem _

theorem coeff_add_mem (S : Subalgebra k T) (u v : TruncatedWittVector p n T)
    (hu : ∀ j, u.coeff j ∈ S) (hv : ∀ j, v.coeff j ∈ S) (i : Fin n) : (u + v).coeff i ∈ S := by
  have hu' : WittVector.truncate n u.out = u := TruncatedWittVector.truncateFun_out u
  have hv' : WittVector.truncate n v.out = v := TruncatedWittVector.truncateFun_out v
  rw [← hu', ← hv', ← map_add, WittVector.coeff_truncate, WittVector.add_coeff]
  unfold WittVector.peval
  rw [MvPolynomial.aeval_def]
  refine MvPolynomial.eval₂_mem (fun m _ => ?_) (fun ij => ?_)
  · rw [eq_intCast]; exact intCast_mem S _
  · obtain ⟨a, j⟩ := ij
    change (![u.out.coeff, v.out.coeff] a) j ∈ S
    fin_cases a
    · exact coeff_out_mem S u hu j
    · exact coeff_out_mem S v hv j

theorem coeff_neg_mem (S : Subalgebra k T) (u : TruncatedWittVector p n T)
    (hu : ∀ j, u.coeff j ∈ S) (i : Fin n) : (-u).coeff i ∈ S := by
  have hu' : WittVector.truncate n u.out = u := TruncatedWittVector.truncateFun_out u
  rw [← hu', ← map_neg, WittVector.coeff_truncate, WittVector.neg_coeff]
  unfold WittVector.peval
  rw [MvPolynomial.aeval_def]
  refine MvPolynomial.eval₂_mem (fun m _ => ?_) (fun ij => ?_)
  · rw [eq_intCast]; exact intCast_mem S _
  · obtain ⟨a, j⟩ := ij
    change (![u.out.coeff] a) j ∈ S
    fin_cases a
    exact coeff_out_mem S u hu j

end WittPoly
p2m_reactivate "P2MW.S_Deformation_adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual.Ideal P2MW.S_Deformation_adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual.HopfAlgebra.HopfIdealQuotient P2MW.S_Deformation_adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual.HopfAlgebra"

section Sub

variable (k : Type u) [Field k] (p : ℕ) [hp : Fact p.Prime]
variable (B : Type v) [CommRing B] [HopfAlgebra k B]

def coords : Set B :=
  {b : B | ∃ (n : ℕ) (x : wittHom k p n B) (i : Fin n), (x : TruncatedWittVector p n B).coeff i = b}

def Bsub : Subalgebra k B := Algebra.adjoin k (coords k p B)

variable {k p B}

theorem coeff_mem_Bsub {n : ℕ} (x : wittHom k p n B) (i : Fin n) :
    (x : TruncatedWittVector p n B).coeff i ∈ Bsub k p B :=
  Algebra.subset_adjoin ⟨n, x, i, rfl⟩

theorem counit_eq_zero_of_mem_coords {b : B} (hb : b ∈ coords k p B) : counit (R := k) b = 0 := by
  obtain ⟨n, x, i, rfl⟩ := hb
  exact counit_coeff_of_mem_wittHom x.2 i

theorem comul_coeff_mem_range {n : ℕ} (x : wittHom k p n B) (i : Fin n) :
    comul (R := k) ((x : TruncatedWittVector p n B).coeff i) ∈
      (Algebra.TensorProduct.map (Bsub k p B).val (Bsub k p B).val).range := by
  have hx := (mem_wittHom_iff (x : TruncatedWittVector p n B)).1 x.2
  have h1 : comul (R := k) ((x : TruncatedWittVector p n B).coeff i) =
      (TruncWitt.map (comulRingHom k B) (x : TruncatedWittVector p n B)).coeff i := by
    rw [TruncWitt.coeff_map]; rfl
  rw [h1, hx]
  refine coeff_add_mem _ _ _ (fun j => ?_) (fun j => ?_) i
  · rw [TruncWitt.coeff_map]
    exact ⟨⟨_, coeff_mem_Bsub x j⟩ ⊗ₜ[k] 1, by simp⟩
  · rw [TruncWitt.coeff_map]
    exact ⟨1 ⊗ₜ[k] ⟨_, coeff_mem_Bsub x j⟩, by simp⟩

theorem convMul_id_antipode :
    WithConv.toConv (AlgHom.id k B) *
      WithConv.toConv (HopfAlgebra.HopfIdealQuotient.sAlgHom k (H := B)) = 1 := by
  apply WithConv.ext
  refine AlgHom.ext fun x => ?_
  change (WithConv.toConv (AlgHom.id k B) *
    WithConv.toConv (HopfAlgebra.HopfIdealQuotient.sAlgHom k (H := B))) x = (1 : WithConv (B →ₐ[k] B)) x
  rw [AlgHom.convMul_apply, AlgHom.convOne_apply]
  have : ∀ z : B ⊗[k] B, Algebra.TensorProduct.lift (AlgHom.id k B)
      (HopfAlgebra.HopfIdealQuotient.sAlgHom k (H := B)) (fun _ _ => .all _ _) z =
      LinearMap.mul' k B ((HopfAlgebra.antipode k).lTensor B z) := by
    intro z
    induction z with
    | zero => simp
    | tmul a b => simp [LinearMap.lTensor_tmul]
    | add a b ha hb => simp only [map_add, ha, hb]
  rw [this, HopfAlgebra.mul_antipode_lTensor_comul_apply]

theorem map_antipode_eq_neg {n : ℕ} (x : wittHom k p n B) :
    TruncWitt.map (HopfAlgebra.HopfIdealQuotient.sAlgHom k (H := B)).toRingHom
      (x : TruncatedWittVector p n B) = -(x : TruncatedWittVector p n B) := by
  have h := map_convMul_of_mem_wittHom (T := B) x.2 (WithConv.toConv (AlgHom.id k B))
    (WithConv.toConv (HopfAlgebra.HopfIdealQuotient.sAlgHom k (H := B)))
  rw [convMul_id_antipode] at h

  have h0 : TruncWitt.map (1 : WithConv (B →ₐ[k] B)).ofConv.toRingHom (x : TruncatedWittVector p n B) = 0 := by
    have hfac : (1 : WithConv (B →ₐ[k] B)).ofConv.toRingHom =
        (algebraMap k B).comp (Bialgebra.counitAlgHom k B).toRingHom := by
      refine RingHom.ext fun c => ?_
      simp [AlgHom.convOne_apply]
    rw [hfac, ← TruncWitt.map_map, map_counit_of_mem_wittHom x.2, map_zero]
  rw [h0] at h
  have hid : TruncWitt.map (WithConv.toConv (AlgHom.id k B)).ofConv.toRingHom
      (x : TruncatedWittVector p n B) = x := TruncWitt.map_id _
  rw [hid] at h
  exact (eq_neg_of_add_eq_zero_right h.symm)

theorem antipode_coeff_mem {n : ℕ} (x : wittHom k p n B) (i : Fin n) :
    HopfAlgebra.antipode k ((x : TruncatedWittVector p n B).coeff i) ∈ Bsub k p B := by
  have : HopfAlgebra.antipode k ((x : TruncatedWittVector p n B).coeff i) =
      (TruncWitt.map (HopfAlgebra.HopfIdealQuotient.sAlgHom k (H := B)).toRingHom
        (x : TruncatedWittVector p n B)).coeff i := by
    rw [TruncWitt.coeff_map]; rfl
  rw [this, map_antipode_eq_neg]
  exact coeff_neg_mem _ _ (fun j => coeff_mem_Bsub x j) i

theorem isHopfSubalgebra_Bsub : HopfAlgebra.IsHopfSubalgebra k (Bsub k p B) where
  comul_mem := by
    intro y hy
    rw [← HopfAlgebra.IsHopfSubalgebra.range_ι₂]

    have hsub : Bsub k p B ≤ ((Algebra.TensorProduct.map (Bsub k p B).val (Bsub k p B).val).range).comap
        (Bialgebra.comulAlgHom k B) := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨n, x, i, rfl⟩
      rw [Subalgebra.coe_comap, Set.mem_preimage, SetLike.mem_coe]
      exact comul_coeff_mem_range x i
    have := hsub hy
    rw [Subalgebra.mem_comap] at this
    obtain ⟨z, hz⟩ := this
    exact ⟨z, hz⟩
  antipode_mem := by
    intro y hy
    have hsub : Bsub k p B ≤ (Bsub k p B).comap (HopfAlgebra.HopfIdealQuotient.sAlgHom k (H := B)) := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨n, x, i, rfl⟩
      rw [Subalgebra.coe_comap, Set.mem_preimage, SetLike.mem_coe]
      exact antipode_coeff_mem x i
    exact hsub hy

end Sub
p2m_reactivate "P2MW.S_Deformation_adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual.Ideal P2MW.S_Deformation_adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual.HopfAlgebra.HopfIdealQuotient P2MW.S_Deformation_adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual.HopfAlgebra"

section HopfIdealOfSub

variable {k : Type u} [Field k] {B : Type v} [CommRing B] [HopfAlgebra k B]
variable (K : Subalgebra k B) (hK : HopfAlgebra.IsHopfSubalgebra k K)

def augIdealOf : Ideal B := Ideal.span {b : B | b ∈ K ∧ counit (R := k) b = 0}

theorem quotient_mk_eq_of_mem {b : B} (hb : b ∈ K) :
    Ideal.Quotient.mk (augIdealOf (k := k) K) b = algebraMap k _ (counit (R := k) b) := by
  have hmem : b - algebraMap k B (counit (R := k) b) ∈ augIdealOf (k := k) K :=
    Ideal.subset_span ⟨sub_mem hb (Subalgebra.algebraMap_mem K _), by simp⟩
  rw [← sub_eq_zero, ← Ideal.Quotient.mk_algebraMap, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact hmem

theorem mkₐ_comp_val :
    (Ideal.Quotient.mkₐ k (augIdealOf (k := k) K)).comp K.val =
      (Algebra.ofId k _).comp ((Bialgebra.counitAlgHom k B).comp K.val) := by
  refine AlgHom.ext fun s => ?_
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Subalgebra.coe_val,
    Bialgebra.counitAlgHom_apply, Algebra.ofId_apply]
  exact quotient_mk_eq_of_mem K s.2

theorem map_counit_counit_comul (y : B) :
    TensorProduct.map (Bialgebra.counitAlgHom k B).toLinearMap (Bialgebra.counitAlgHom k B).toLinearMap
      (comul (R := k) y) = (1 : k) ⊗ₜ[k] counit (R := k) y := by
  have h := Coalgebra.rTensor_counit_comul (R := k) y
  have := congrArg ((counit (R := k) (A := B)).lTensor k) h
  rw [LinearMap.lTensor_tmul, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor] at this
  exact this

include hK in

theorem isHopfIdeal_augIdealOf : (augIdealOf (k := k) K).IsHopfIdeal' k where
  map_mkₐ_comul_eq_zero := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨hyK, hyε⟩ := hy
      have hΔ := hK.comul_mem y hyK
      rw [← HopfAlgebra.IsHopfSubalgebra.range_ι₂] at hΔ
      obtain ⟨z, hz⟩ := hΔ
      have hz' : Algebra.TensorProduct.map K.val K.val z = comul (R := k) y := hz
      rw [← hz', ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, mkₐ_comp_val,
        Algebra.TensorProduct.map_comp, AlgHom.comp_apply]
      have h2 : Algebra.TensorProduct.map ((Bialgebra.counitAlgHom k B).comp K.val)
          ((Bialgebra.counitAlgHom k B).comp K.val) z = (1 : k) ⊗ₜ[k] counit (R := k) y := by
        rw [Algebra.TensorProduct.map_comp, AlgHom.comp_apply, hz', ← map_counit_counit_comul]
        rfl
      rw [h2, hyε, TensorProduct.tmul_zero, map_zero]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, add_zero]
    | smul a x _ hx =>
      rw [smul_eq_mul, ← Bialgebra.comulAlgHom_apply, map_mul, map_mul, Bialgebra.comulAlgHom_apply,
        Bialgebra.comulAlgHom_apply, hx, mul_zero]
  counit_eq_zero := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact hy.2
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul a x _ hx => rw [smul_eq_mul, counit_mul, hx, mul_zero]
  antipode_mem := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      exact Ideal.subset_span ⟨hK.antipode_mem y hy.1, by rw [HopfAlgebra.counit_antipode, hy.2]⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [smul_eq_mul, HopfAlgebra.antipode_mul]; exact Ideal.mul_mem_right _ _ hx

end HopfIdealOfSub
p2m_reactivate "P2MW.S_Deformation_adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual.Ideal P2MW.S_Deformation_adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual.HopfAlgebra.HopfIdealQuotient P2MW.S_Deformation_adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual.HopfAlgebra"

section RightExact

open WithConv

variable {k : Type u} [Field k] {B : Type v} [CommRing B] [Bialgebra k B] [Coalgebra.IsCocomm k B]

theorem mem_maximalIdeal_of_apply_one_eq_zero
    (hloc : IsLocalRing (CartierDual k B)) (φ : CartierDual k B) (hφ : φ 1 = 0) :
    φ ∈ IsLocalRing.maximalIdeal (CartierDual k B) := by
  haveI := hloc
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨ψ', hψ'⟩ := hu.exists_right_inv
  have h1 := congrArg (fun χ : CartierDual k B => χ 1) hψ'
  rw [CartierDual.mul_apply, Bialgebra.comul_one, Algebra.TensorProduct.one_def,
    TensorProduct.dualDistrib_apply, CartierDual.one_apply, Bialgebra.counit_one,
    CartierDual.toDual_apply, hφ, zero_mul] at h1
  exact zero_ne_one h1

theorem toConv_toDual_pow (φ : CartierDual k B) :
    ∀ m : ℕ, toConv (CartierDual.toDual k B (φ ^ m)) = (toConv (CartierDual.toDual k B φ)) ^ m
  | 0 => by
    rw [pow_zero, pow_zero]
    apply WithConv.ext
    rw [ofConv_toConv, CartierDual.convOne_ofConv_eq_counit]
    rfl
  | m + 1 => by
    rw [pow_succ, pow_succ, ← toConv_toDual_pow φ m, CartierDual.toDual_mul, toConv_ofConv]

variable [Module.Finite k B]

theorem isNilpotent_maximalIdeal (hloc : IsLocalRing (CartierDual k B)) :
    IsNilpotent (IsLocalRing.maximalIdeal (CartierDual k B)) := by
  haveI := hloc
  haveI : IsArtinianRing (CartierDual k B) := IsArtinianRing.of_finite k (CartierDual k B)
  have h := IsArtinianRing.isNilpotent_jacobson_bot (R := CartierDual k B)
  rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at h

theorem exists_forall_convPow_eq_zero (p : ℕ) [Fact p.Prime] (hloc : IsLocalRing (CartierDual k B)) :
    ∃ N : ℕ, ∀ β : WithConv (B →ₗ[k] k), β.ofConv 1 = 0 → β ^ p ^ N = 0 := by
  haveI := hloc
  obtain ⟨N, hN⟩ := isNilpotent_maximalIdeal (k := k) (B := B) hloc
  refine ⟨N, fun β hβ => ?_⟩
  set φ : CartierDual k B := CartierDual.ofDual k B β.ofConv with hφdef
  have hφ : φ ∈ IsLocalRing.maximalIdeal (CartierDual k B) :=
    mem_maximalIdeal_of_apply_one_eq_zero hloc φ hβ
  have hφN : φ ^ N = 0 := by
    have : φ ^ N ∈ IsLocalRing.maximalIdeal (CartierDual k B) ^ N := Ideal.pow_mem_pow hφ N
    rwa [hN, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  have hφpN : φ ^ p ^ N = 0 := by
    have hle : N ≤ p ^ N := (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hle
    rw [hc, pow_add, hφN, zero_mul]
  have hβφ : β = toConv (CartierDual.toDual k B φ) := by
    rw [hφdef, CartierDual.toDual_ofDual, toConv_ofConv]
  rw [hβφ, ← toConv_toDual_pow, hφpN, map_zero]
  rfl

end RightExact
p2m_reactivate "P2MW.S_Deformation_adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual.Ideal P2MW.S_Deformation_adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual.HopfAlgebra.HopfIdealQuotient P2MW.S_Deformation_adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual.HopfAlgebra"

section RightExactM

variable (k : Type u) [Field k] [PerfectField k] (p : ℕ) [hp : Fact p.Prime] [CharP k p]

theorem map_surjective_of_isLocalRing
    {B : Type v} [CommRing B] [HopfAlgebra k B] [Coalgebra.IsCocomm k B] [Module.Finite k B]
    {Q : Type w} [CommRing Q] [Bialgebra k Q] (π : B →ₐc[k] Q) (hπ : Surjective π)
    (hB : IsLocalRing (CartierDual k B)) : Surjective (DieudonneModule.map k p π) := by
  obtain ⟨N, hN⟩ := exists_forall_convPow_eq_zero (k := k) (B := B) p hB
  intro z
  obtain ⟨m, y, rfl⟩ := exists_of z

  have hV : ∀ β : WithConv (B →ₗ[k] k), β.ofConv 1 = 0 → β ^ p ^ (N + (m + 1)) = 0 := fun β hβ => by
    rw [pow_add, pow_mul, hN β hβ, zero_pow (pow_ne_zero _ hp.out.ne_zero)]
  haveI : NeZero (N + (m + 1)) := ⟨Nat.succ_ne_zero _⟩
  have hmL : m ≤ N + (m + 1) := by omega
  obtain ⟨x, hx⟩ :=
    HopfAlgebra.wittHomMap_surjective_of_surjective_of_forall_convPow_eq_zero k p (N + (m + 1)) B Q π
      hπ hV (wittHomShiftLE k p Q hmL y)
  exact ⟨of k p B (N + (m + 1)) x, by rw [map_of, hx, of_shiftLE]⟩

end RightExactM
p2m_reactivate "P2MW.S_Deformation_adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual.Ideal P2MW.S_Deformation_adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual.HopfAlgebra.HopfIdealQuotient P2MW.S_Deformation_adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual.HopfAlgebra"

section Kernel

variable (k : Type u) [Field k] [PerfectField k] (p : ℕ) [hp : Fact p.Prime] [CharP k p]
variable (B : Type v) [CommRing B] [HopfAlgebra k B] [Coalgebra.IsCocomm k B] [Module.Finite k B]

theorem mem_augIdealOf_of_counit_eq_zero (hB : IsLocalRing (CartierDual k B)) (b : B)
    (hb : counit (R := k) b = 0) : b ∈ augIdealOf (k := k) (Bsub k p B) := by
  by_contra hbI
  set I : Ideal B := augIdealOf (k := k) (Bsub k p B) with hIdef
  haveI hI : I.IsHopfIdeal' k := isHopfIdeal_augIdealOf _ isHopfSubalgebra_Bsub
  let π : B →ₐc[k] (B ⧸ I) := HopfAlgebra.HopfIdealQuotient.quotientBialgHom k I
  have hπ : Surjective π := Ideal.Quotient.mk_surjective

  have hQ1 : Module.finrank k (B ⧸ I) ≠ 1 := by
    intro hQ1
    have hs : Surjective (Bialgebra.counitAlgHom k (B ⧸ I)).toLinearMap := fun r =>
      ⟨algebraMap k (B ⧸ I) r, by simp⟩
    have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [hQ1, Module.finrank_self]) (f := (Bialgebra.counitAlgHom k (B ⧸ I)).toLinearMap)).2 hs
    apply hbI
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply hinj
    change Coalgebra.counit (R := k) (Ideal.Quotient.mk I b) = Coalgebra.counit (R := k) (0 : B ⧸ I)
    rw [map_zero, HopfAlgebra.HopfIdealQuotient.coalgebra_counit_mk, hb]

  have hQ : IsLocalRing (CartierDual k (B ⧸ I)) :=
    HopfAlgebra.isLocalRing_cartierDual_of_surjective k B (B ⧸ I) π hπ hB
  obtain ⟨a, ha0, ha⟩ :=
    HopfAlgebra.exists_ne_zero_comul_eq_tmul_one_add_one_tmul_of_isLocalRing_cartierDual k (B ⧸ I) hQ hQ1
  have hamem : a ∈ primitives k (B ⧸ I) := by
    change a ∈ LinearMap.ker _
    rw [LinearMap.mem_ker]
    simp [ha]
  let xa : wittHom k p 1 (B ⧸ I) := ⟨TruncatedWittVector.mk p fun _ => a,
    (Deformation.mem_wittHom_one_iff_coeff_mem_primitives k p (B ⧸ I) _).2 (by simpa using hamem)⟩

  obtain ⟨z, hz⟩ := map_surjective_of_isLocalRing k p π hπ hB (of k p (B ⧸ I) 1 xa)
  obtain ⟨n, x, rfl⟩ := exists_of z
  rw [map_of] at hz
  have hx0 : wittHomMap p n π x = 0 := by
    apply Subtype.ext
    refine TruncatedWittVector.ext fun i => ?_
    rw [coe_wittHomMap, TruncWitt.coeff_map, ZeroMemClass.coe_zero, TruncatedWittVector.coeff_zero]
    change Ideal.Quotient.mk I ((x : TruncatedWittVector p n B).coeff i) = 0
    rw [quotient_mk_eq_of_mem (Bsub k p B) (coeff_mem_Bsub x i), counit_coeff_of_mem_wittHom x.2 i,
      map_zero]
  rw [hx0, map_zero] at hz
  have hxa : xa = 0 := of_injective 1 (hz.symm.trans (map_zero _).symm)
  apply ha0
  have := congrArg (fun t : wittHom k p 1 (B ⧸ I) => (t : TruncatedWittVector p 1 (B ⧸ I)).coeff 0) hxa
  simpa [xa] using this

end Kernel
p2m_reactivate "P2MW.S_Deformation_adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual.Ideal P2MW.S_Deformation_adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual.HopfAlgebra.HopfIdealQuotient P2MW.S_Deformation_adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual.HopfAlgebra"

section Takeuchi

variable {k : Type u} [Field k] {B : Type v} [CommRing B] [HopfAlgebra k B] [Module.Finite k B]
variable (K : Subalgebra k B) (hK : HopfAlgebra.IsHopfSubalgebra k K)

include hK in
theorem eq_top_of_forall_mem_augIdealOf (h : ∀ b : B, counit (R := k) b = 0 → b ∈ augIdealOf (k := k) K) :
    K = ⊤ := by
  letI := hK.hopfAlgebra
  haveI := hK.isHopfTower
  have hff : Module.FaithfullyFlat ↥K B :=
    HopfAlgebra.faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem K hK.comul_mem hK.antipode_mem

  set J : Ideal B := HopfAlgebra.HopfTower.augIdealMap k ↥K B with hJ
  have hJmem : ∀ b : B, b - algebraMap k B (counit (R := k) b) ∈ J := by
    intro b
    have hle : augIdealOf (k := k) K ≤ J := by
      refine Ideal.span_le.2 ?_
      rintro c ⟨hcK, hcε⟩
      exact HopfAlgebra.HopfTower.algebraMap_mem_augIdealMap k ↥K B (a := ⟨c, hcK⟩) hcε
    exact hle (h _ (by simp))
  have hmk : ∀ b : B, Ideal.Quotient.mk J b = algebraMap k _ (counit (R := k) b) := by
    intro b
    rw [← sub_eq_zero, ← Ideal.Quotient.mk_algebraMap, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact hJmem b

  have hfwd : ∀ b : B, HopfAlgebra.HopfTower.fwdAux k ↥K B B b = b ⊗ₜ[k] 1 := by
    intro b
    rw [HopfAlgebra.HopfTower.fwdAux_apply k ↥K B B (ℛ k b)]
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    rw [← hJ]
    simp_rw [hmk, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      ← TensorProduct.sum_tmul]
    rw [HopfAlgebra.sum_counit_right_smul k B (ℛ k b)]

  have hform : ∀ t : B ⊗[k] (B ⧸ J), ∃ c : B, t = c ⊗ₜ[k] 1 := by
    intro t
    induction t with
    | zero => exact ⟨0, by simp⟩
    | tmul c d =>
      obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective d
      exact ⟨counit (R := k) d • c, by rw [hmk, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul']⟩
    | add x y hx hy =>
      obtain ⟨c, rfl⟩ := hx; obtain ⟨c', rfl⟩ := hy
      exact ⟨c + c', by rw [TensorProduct.add_tmul]⟩

  have hsurj : ∀ t : B ⊗[↥K] B, ∃ c : B, t = (1 : B) ⊗ₜ[↥K] c := by
    intro t
    obtain ⟨c, hc⟩ := hform (HopfAlgebra.HopfTower.galoisEquiv k ↥K B B t)
    refine ⟨c, (HopfAlgebra.HopfTower.galoisEquiv k ↥K B B).injective ?_⟩
    rw [hc, HopfAlgebra.HopfTower.galoisEquiv_one_tmul, hfwd]

  let KB : Submodule ↥K B := LinearMap.range (Algebra.linearMap ↥K B)
  haveI : Subsingleton ((B ⧸ KB) ⊗[↥K] B) := by
    refine ⟨fun s t => ?_⟩
    suffices hzero : ∀ s : (B ⧸ KB) ⊗[↥K] B, s = 0 by rw [hzero s, hzero t]
    intro s
    obtain ⟨s', rfl⟩ := LinearMap.rTensor_surjective B (Submodule.mkQ_surjective KB) s
    obtain ⟨c, rfl⟩ := hsurj s'
    rw [LinearMap.rTensor_tmul, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero KB).2 ⟨1, by simp⟩, TensorProduct.zero_tmul]
  haveI : Subsingleton (B ⧸ KB) := Module.FaithfullyFlat.rTensor_reflects_triviality ↥K B (B ⧸ KB)
  rw [eq_top_iff]
  intro b _
  have : Submodule.Quotient.mk (p := KB) b = 0 := Subsingleton.elim _ _
  rw [Submodule.Quotient.mk_eq_zero] at this
  obtain ⟨s, hs⟩ := this
  rw [← hs]
  exact s.2

end Takeuchi
p2m_reactivate "P2MW.S_Deformation_adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual.Ideal P2MW.S_Deformation_adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual.HopfAlgebra.HopfIdealQuotient P2MW.S_Deformation_adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual.HopfAlgebra"

end DieudonneEmb
p2m_reactivate "P2MW.S_Deformation_adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual.Ideal P2MW.S_Deformation_adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual.HopfAlgebra.HopfIdealQuotient P2MW.S_Deformation_adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual.HopfAlgebra"

open DieudonneEmb in
theorem solution
    (k : Type u) [Field k] [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (B : Type v) [CommRing B] [HopfAlgebra k B] [Coalgebra.IsCocomm k B] [Module.Finite k B]
    (hB : IsLocalRing (CartierDual k B)) :
    Algebra.adjoin k {b : B | ∃ (n : ℕ) (x : Deformation.wittHom k p n B) (i : Fin n),
        (x : TruncatedWittVector p n B).coeff i = b} = ⊤ :=
  eq_top_of_forall_mem_augIdealOf (Bsub k p B) isHopfSubalgebra_Bsub
    (mem_augIdealOf_of_counit_eq_zero k p B hB)

end
end S_Deformation_adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual
end P2MW
export P2MW.S_Deformation_adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual (solution)
