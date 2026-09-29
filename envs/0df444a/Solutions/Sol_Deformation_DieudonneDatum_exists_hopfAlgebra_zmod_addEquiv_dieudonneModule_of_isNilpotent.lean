-- Prove2me | solution 1 for Deformation.DieudonneDatum.exists_hopfAlgebra_zmod_addEquiv_dieudonneModule_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/c5389f93-3828-500f-8ffa-bca352e2e3ec

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_Dieudonne_WittGroupHopf
import Definitions.Def_HopfAlgebra_HopfIdealQuotient
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Definitions.Def_Dieudonne_WittKernelHopf
import Theorems.Thm_Deformation_convPow_eq_zero_and_isLocalRing_cartierDual_of_adjoin_coeff_wittHom_eq_top
import Theorems.Thm_Deformation_WittKernel_addSubgroup_eq_top_and_exists_addMonoidHom_apply_tautoClass_eq_of_pow_eq
import Theorems.Thm_Deformation_DieudonneModule_map_injective_and_exists_map_eq_of_isLocalRing_cartierDual
import Theorems.Thm_Deformation_DieudonneModule_map_surjective_and_exact_map_of_ker_eq_map_ker_counit
import Theorems.Thm_HopfAlgebra_isLocalRing_cartierDual_of_surjective
import Theorems.Thm_Deformation_DieudonneModule_exists_finrank_eq_pow_and_natCard_eq_pow_of_isLocalRing_cartierDual
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_DieudonneDatum_exists_hopfAlgebra_zmod_addEquiv_dieudonneModule_of_isNilpotent
p2m_attr_erase "instance" "CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.IsHopfTower.refl"
p2m_attr_erase "simp" "ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul"

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

noncomputable section

open Function
open scoped TensorProduct

namespace DieudonneFiniteZMod

theorem exists_lt_pow_eq {D : Type*} [AddCommGroup D] [Finite D] (F : D →ₗ[ℤ] D) :
    ∃ a b : ℕ, a < b ∧ F ^ b = F ^ a := by
  have h := Finite.exists_ne_map_eq_of_infinite (fun c : ℕ => (⇑(F ^ c) : D → D))
  obtain ⟨c, c', hne, heq⟩ := h
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact ⟨c, c', hlt, LinearMap.ext fun x => (congrFun heq x).symm⟩
  · exact ⟨c', c, hlt, LinearMap.ext fun x => congrFun heq x⟩

section HopfIdeals

open Coalgebra Bialgebra WithConv HopfAlgebra

variable {R : Type*} [CommRing R]
variable {H : Type*} [CommRing H] [HopfAlgebra R H]
variable {H' : Type*} [CommRing H'] [HopfAlgebra R H']
variable {B : Type*} [CommRing B] [HopfAlgebra R B]

theorem isHopfIdeal_span (T : Set H)
    (hΔ : ∀ x ∈ T, Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R (Ideal.span T))
        (Ideal.Quotient.mkₐ R (Ideal.span T)) (comul (R := R) x) = 0)
    (hε : ∀ x ∈ T, counit (R := R) x = 0)
    (hS : ∀ x ∈ T, antipode R x ∈ Ideal.span T) :
    (Ideal.span T).IsHopfIdeal' R where
  map_mkₐ_comul_eq_zero := by
    intro x hx
    let Φ : H →ₐ[R] (H ⧸ Ideal.span T) ⊗[R] (H ⧸ Ideal.span T) :=
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R (Ideal.span T))
        (Ideal.Quotient.mkₐ R (Ideal.span T))).comp (comulAlgHom R H)
    change Φ x = 0
    induction hx using Submodule.span_induction with
    | mem y hy => exact hΔ y hy
    | zero => exact map_zero Φ
    | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
    | smul a y _ hy => rw [smul_eq_mul, map_mul, hy, mul_zero]
  counit_eq_zero := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact hε y hy
    | zero => exact map_zero _
    | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
    | smul a y _ hy => rw [smul_eq_mul, Bialgebra.counit_mul, hy, mul_zero]
  antipode_mem := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact hS y hy
    | zero => rw [map_zero]; exact Ideal.zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact Ideal.add_mem _ hy hz
    | smul a y _ hy =>
      rw [smul_eq_mul, ← antipodeAlgHom_apply, map_mul]
      exact Ideal.mul_mem_left _ _ hy

theorem isHopfIdeal_ker_of_surjective (φ : H →ₐc[R] B) (hφ : Function.Surjective φ) :
    (RingHom.ker (φ : H →ₐ[R] B)).IsHopfIdeal' R where
  map_mkₐ_comul_eq_zero := by
    intro x hx
    have hx0 : φ x = 0 := hx
    let e : (H ⧸ RingHom.ker (φ : H →ₐ[R] B)) ≃ₐ[R] B := Ideal.quotientKerAlgEquivOfSurjective hφ
    have hmk : Ideal.Quotient.mkₐ R (RingHom.ker (φ : H →ₐ[R] B)) =
        ((e.symm : B →ₐ[R] H ⧸ RingHom.ker (φ : H →ₐ[R] B)).comp (φ : H →ₐ[R] B)) := by
      refine AlgHom.ext fun y => ?_
      rw [AlgHom.comp_apply]
      change Ideal.Quotient.mk (RingHom.ker (φ : H →ₐ[R] B)) y = e.symm (φ y)
      apply e.injective
      rw [AlgEquiv.apply_symm_apply]
      exact Ideal.quotientKerAlgEquivOfSurjective_mk hφ y
    rw [hmk, Algebra.TensorProduct.map_comp, AlgHom.comp_apply]
    have hco : Algebra.TensorProduct.map (φ : H →ₐ[R] B) (φ : H →ₐ[R] B) (comul (R := R) x) =
        comul (R := R) (φ x) :=
      (DFunLike.congr_fun (BialgHom.map_comp_comulAlgHom φ) x)
    rw [hco, hx0, map_zero, map_zero]
  counit_eq_zero := by
    intro x hx
    have hx0 : φ x = 0 := hx
    rw [← CoalgHomClass.counit_comp_apply φ x, hx0, map_zero]
  antipode_mem := by
    intro x hx
    have hx0 : φ x = 0 := hx
    change φ (antipode R x) = 0
    rw [HopfAlgebra.map_antipode φ, hx0, map_zero]

theorem isHopfIdeal_map (ψ : H →ₐc[R] H') (I : Ideal H) [hI : I.IsHopfIdeal' R] :
    (I.map (ψ : H →ₐ[R] H')).IsHopfIdeal' R := by
  have hspan : Ideal.span ((ψ : H →ₐ[R] H') '' (I : Set H)) = I.map (ψ : H →ₐ[R] H') := rfl
  rw [← hspan]
  refine isHopfIdeal_span _ ?_ ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    set J : Ideal H' := Ideal.span ((ψ : H →ₐ[R] H') '' (I : Set H)) with hJ
    have hIJ : I ≤ J.comap (ψ : H →ₐ[R] H') := by
      intro y hy
      exact Ideal.subset_span ⟨y, hy, rfl⟩
    let ψbar : (H ⧸ I) →ₐ[R] (H' ⧸ J) := Ideal.quotientMapₐ J (ψ : H →ₐ[R] H') hIJ
    have hmk : (Ideal.Quotient.mkₐ R J).comp (ψ : H →ₐ[R] H') = ψbar.comp (Ideal.Quotient.mkₐ R I) :=
      (Ideal.quotient_map_comp_mkₐ J (ψ : H →ₐ[R] H') hIJ).symm
    have hco : comul (R := R) ((ψ : H →ₐ[R] H') x) =
        Algebra.TensorProduct.map (ψ : H →ₐ[R] H') (ψ : H →ₐ[R] H') (comul (R := R) x) :=
      (DFunLike.congr_fun (BialgHom.map_comp_comulAlgHom ψ) x).symm
    change Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R J) (Ideal.Quotient.mkₐ R J)
      (comul (R := R) ((ψ : H →ₐ[R] H') x)) = 0
    rw [hco, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, hmk, Algebra.TensorProduct.map_comp,
      AlgHom.comp_apply, hI.map_mkₐ_comul_eq_zero x hx, map_zero]
  · rintro _ ⟨x, hx, rfl⟩
    change counit (R := R) (ψ x) = 0
    rw [CoalgHomClass.counit_comp_apply, hI.counit_eq_zero x hx]
  · rintro _ ⟨x, hx, rfl⟩
    change antipode R (ψ x) ∈ _
    rw [← HopfAlgebra.map_antipode ψ]
    exact Ideal.subset_span ⟨_, hI.antipode_mem x hx, rfl⟩

scoped instance isHopfIdeal_ker_counit : (RingHom.ker (Bialgebra.counitAlgHom R H)).IsHopfIdeal' R := by
  have h : RingHom.ker (Bialgebra.counitAlgHom R H) =
      RingHom.ker ((Bialgebra.counitBialgHom R H : H →ₐc[R] R) : H →ₐ[R] R) := rfl
  rw [h]
  refine isHopfIdeal_ker_of_surjective _ fun r => ⟨algebraMap R H r, ?_⟩
  change Coalgebra.counit (algebraMap R H r) = r
  exact Bialgebra.counit_algebraMap r

scoped instance isHopfIdeal_map_ker_counit (g : H →ₐc[R] H') :
    ((RingHom.ker (Bialgebra.counitAlgHom R H)).map (g : H →ₐ[R] H')).IsHopfIdeal' R :=
  isHopfIdeal_map g _

end HopfIdeals

section TwoSurjections

variable {M N N' : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup N']

def equivOfSurjective (ψ : M →+ N) (π : M →+ N') (hψ : Function.Surjective ψ)
    (hπ : Function.Surjective π) (hker : ψ.ker = π.ker) : N ≃+ N' :=
  ((QuotientAddGroup.quotientKerEquivOfSurjective ψ hψ).symm.trans
    (QuotientAddGroup.quotientAddEquivOfEq hker)).trans (QuotientAddGroup.quotientKerEquivOfSurjective π hπ)

theorem equivOfSurjective_apply (ψ : M →+ N) (π : M →+ N') (hψ : Function.Surjective ψ)
    (hπ : Function.Surjective π) (hker : ψ.ker = π.ker) (m : M) :
    equivOfSurjective ψ π hψ hπ hker (ψ m) = π m := by
  unfold equivOfSurjective
  rw [AddEquiv.trans_apply, AddEquiv.trans_apply]
  have h1 : (QuotientAddGroup.quotientKerEquivOfSurjective ψ hψ).symm (ψ m) = QuotientAddGroup.mk m := by
    apply (QuotientAddGroup.quotientKerEquivOfSurjective ψ hψ).injective
    rw [AddEquiv.apply_symm_apply]
    rfl
  rw [h1]
  rfl

end TwoSurjections

section Relations

variable (p : ℕ) [Fact p.Prime]
variable {A : Type} [CommRing A] [HopfAlgebra (ZMod p) A]

open Deformation

theorem datum_F_pow_apply (c : ℕ) (z : DieudonneModule (ZMod p) p A) :
    ((DieudonneModule.dieudonneDatum (ZMod p) p A).F ^ c) z =
      (DieudonneModule.frobenius (ZMod p) p A)^[c] z := by
  rw [Module.End.pow_apply]
  induction c generalizing z with
  | zero => rfl
  | succ c ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    rfl

theorem datum_V_pow_apply (c : ℕ) (z : DieudonneModule (ZMod p) p A) :
    ((DieudonneModule.dieudonneDatum (ZMod p) p A).V ^ c) z =
      (DieudonneModule.verschiebung (ZMod p) p A)^[c] z := by
  rw [Module.End.pow_apply]
  induction c generalizing z with
  | zero => rfl
  | succ c ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    rfl

theorem frobenius_iterate_verschiebung (c : ℕ) (z : DieudonneModule (ZMod p) p A) :
    (DieudonneModule.frobenius (ZMod p) p A)^[c] (DieudonneModule.verschiebung (ZMod p) p A z) =
      DieudonneModule.verschiebung (ZMod p) p A ((DieudonneModule.frobenius (ZMod p) p A)^[c] z) := by
  induction c generalizing z with
  | zero => rfl
  | succ c ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← ih]
    congr 1

    rw [DieudonneModule.frobenius_verschiebung, DieudonneModule.verschiebung_frobenius]

theorem verschiebung_iterate_frobenius (c : ℕ) (z : DieudonneModule (ZMod p) p A) :
    (DieudonneModule.verschiebung (ZMod p) p A)^[c] (DieudonneModule.frobenius (ZMod p) p A z) =
      DieudonneModule.frobenius (ZMod p) p A ((DieudonneModule.verschiebung (ZMod p) p A)^[c] z) := by
  induction c generalizing z with
  | zero => rfl
  | succ c ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← ih]
    congr 1
    rw [DieudonneModule.frobenius_verschiebung, DieudonneModule.verschiebung_frobenius]

def relSubgroup (n a b : ℕ) : AddSubgroup (DieudonneModule (ZMod p) p A) where
  carrier := {z | (DieudonneModule.verschiebung (ZMod p) p A)^[n] z = 0 ∧
    (DieudonneModule.frobenius (ZMod p) p A)^[b] z = (DieudonneModule.frobenius (ZMod p) p A)^[a] z}
  zero_mem' := by
    refine ⟨?_, ?_⟩
    · exact iterate_map_zero _ n
    · change (DieudonneModule.frobenius (ZMod p) p A)^[b] 0 = (DieudonneModule.frobenius (ZMod p) p A)^[a] 0
      rw [iterate_map_zero, iterate_map_zero]
  add_mem' {x y} hx hy := by
    refine ⟨?_, ?_⟩
    · rw [iterate_map_add, hx.1, hy.1, add_zero]
    · change (DieudonneModule.frobenius (ZMod p) p A)^[b] (x + y) =
        (DieudonneModule.frobenius (ZMod p) p A)^[a] (x + y)
      rw [iterate_map_add, iterate_map_add, hx.2, hy.2]
  neg_mem' {x} hx := by
    refine ⟨?_, ?_⟩
    · rw [iterate_map_neg, hx.1, neg_zero]
    · change (DieudonneModule.frobenius (ZMod p) p A)^[b] (-x) =
        (DieudonneModule.frobenius (ZMod p) p A)^[a] (-x)
      rw [iterate_map_neg, iterate_map_neg, hx.2]

theorem frobenius_mem_relSubgroup (n a b : ℕ) {z : DieudonneModule (ZMod p) p A}
    (hz : z ∈ relSubgroup p n a b) : DieudonneModule.frobenius (ZMod p) p A z ∈ relSubgroup p n a b := by
  refine ⟨?_, ?_⟩
  · rw [verschiebung_iterate_frobenius, hz.1, map_zero]
  · change (DieudonneModule.frobenius (ZMod p) p A)^[b] (DieudonneModule.frobenius (ZMod p) p A z) =
      (DieudonneModule.frobenius (ZMod p) p A)^[a] (DieudonneModule.frobenius (ZMod p) p A z)
    rw [← Function.iterate_succ_apply, Function.iterate_succ_apply', hz.2,
      ← Function.iterate_succ_apply' (f := DieudonneModule.frobenius (ZMod p) p A), Function.iterate_succ_apply]

theorem verschiebung_mem_relSubgroup (n a b : ℕ) {z : DieudonneModule (ZMod p) p A}
    (hz : z ∈ relSubgroup p n a b) :
    DieudonneModule.verschiebung (ZMod p) p A z ∈ relSubgroup p n a b := by
  refine ⟨?_, ?_⟩
  · rw [← Function.iterate_succ_apply, Function.iterate_succ_apply', hz.1, map_zero]
  · change (DieudonneModule.frobenius (ZMod p) p A)^[b] (DieudonneModule.verschiebung (ZMod p) p A z) =
      (DieudonneModule.frobenius (ZMod p) p A)^[a] (DieudonneModule.verschiebung (ZMod p) p A z)
    rw [frobenius_iterate_verschiebung, frobenius_iterate_verschiebung, hz.2]

end Relations

section Main

open Deformation Deformation.WittKernel

variable (p : ℕ) [hp : Fact p.Prime]

abbrev O (n a b : ℕ) (J : Type) : Type := WittKernel.Coord (ZMod p) p n a b J

theorem isLocalRing_O (n a b : ℕ) (J : Type) [Finite J] [Fact (a < b)] :
    IsLocalRing (CartierDual (ZMod p) (O p n a b J)) :=
  (Deformation.convPow_eq_zero_and_isLocalRing_cartierDual_of_adjoin_coeff_wittHom_eq_top (ZMod p) p n
    (O p n a b J) adjoin_coeff_wittHom_eq_top).2

theorem finite_dieudonneModule_O (n a b : ℕ) (J : Type) [Finite J] [Fact (a < b)] :
    Finite (DieudonneModule (ZMod p) p (O p n a b J)) := by
  obtain ⟨L, -, hcard⟩ :=
    Deformation.DieudonneModule.exists_finrank_eq_pow_and_natCard_eq_pow_of_isLocalRing_cartierDual
      (ZMod p) p (O p n a b J) (isLocalRing_O p n a b J)
  refine Nat.finite_of_card_ne_zero ?_
  rw [hcard, Nat.card_zmod]
  exact pow_ne_zero _ hp.out.ne_zero

theorem relSubgroup_O_eq_top (n a b : ℕ) (hab : a < b) (J : Type) [Finite J] :
    relSubgroup p (A := O p n a b J) n a b = ⊤ := by
  haveI : Fact (a < b) := ⟨hab⟩
  have hgen := (Deformation.WittKernel.addSubgroup_eq_top_and_exists_addMonoidHom_apply_tautoClass_eq_of_pow_eq
    p n a b hab J (D := PUnit) ⟨0, 0, by ext, by ext⟩ (by ext) (by ext) (fun _ => PUnit.unit)).1
  refine hgen _ (fun z hz => frobenius_mem_relSubgroup p n a b hz)
    (fun z hz => verschiebung_mem_relSubgroup p n a b hz) (fun j => ⟨?_, ?_⟩)
  · exact verschiebung_iterate_tautoClass j
  · exact frobenius_iterate_tautoClass j

theorem datum_V_pow_O_eq_zero (n a b : ℕ) (hab : a < b) (J : Type) [Finite J] :
    (DieudonneModule.dieudonneDatum (ZMod p) p (O p n a b J)).V ^ n = 0 := by
  refine LinearMap.ext fun z => ?_
  rw [datum_V_pow_apply, LinearMap.zero_apply]
  have hz : z ∈ relSubgroup p (A := O p n a b J) n a b := by
    rw [relSubgroup_O_eq_top p n a b hab J]; trivial
  exact hz.1

theorem datum_F_pow_O_eq (n a b : ℕ) (hab : a < b) (J : Type) [Finite J] :
    (DieudonneModule.dieudonneDatum (ZMod p) p (O p n a b J)).F ^ b =
      (DieudonneModule.dieudonneDatum (ZMod p) p (O p n a b J)).F ^ a := by
  refine LinearMap.ext fun z => ?_
  rw [datum_F_pow_apply, datum_F_pow_apply]
  have hz : z ∈ relSubgroup p (A := O p n a b J) n a b := by
    rw [relSubgroup_O_eq_top p n a b hab J]; trivial
  exact hz.2

theorem exists_realisation {D : Type u} [AddCommGroup D] [Finite D]
    (MD : DieudonneDatum (p : ℤ) D) (n a b : ℕ) (hab : a < b) (hVn : MD.V ^ n = 0)
    (hFab : MD.F ^ b = MD.F ^ a) :
    ∃ (B : Type) (_ : CommRing B) (_ : HopfAlgebra (ZMod p) B) (_ : Coalgebra.IsCocomm (ZMod p) B)
      (_ : Module.Finite (ZMod p) B),
      IsLocalRing (CartierDual (ZMod p) B) ∧
      ∃ e : DieudonneModule (ZMod p) p B ≃+ D,
        (∀ z, e (DieudonneModule.frobenius (ZMod p) p B z) = MD.F (e z)) ∧
        (∀ z, e (DieudonneModule.verschiebung (ZMod p) p B z) = MD.V (e z)) := by
  haveI : Fact (a < b) := ⟨hab⟩

  let J₁ : Type := Fin (Nat.card D)
  let eD : D ≃ J₁ := Finite.equivFin D
  obtain ⟨-, ρ, hρF, hρV, hρτ⟩ :=
    Deformation.WittKernel.addSubgroup_eq_top_and_exists_addMonoidHom_apply_tautoClass_eq_of_pow_eq
      p n a b hab J₁ MD hVn hFab (fun j => eD.symm j)
  have hρsurj : Function.Surjective ρ := fun x =>
    ⟨tautoClass (ZMod p) p n a b J₁ (eD x), by rw [hρτ, Equiv.symm_apply_apply]⟩

  haveI : Finite (DieudonneModule (ZMod p) p (O p n a b J₁)) := finite_dieudonneModule_O p n a b J₁
  let J₂ : Type := ↥(ρ.ker)
  haveI : Finite J₂ := Subtype.finite
  obtain ⟨hgen₂, ρ', hρ'F, hρ'V, hρ'τ⟩ :=
    Deformation.WittKernel.addSubgroup_eq_top_and_exists_addMonoidHom_apply_tautoClass_eq_of_pow_eq
      p n a b hab J₂ (DieudonneModule.dieudonneDatum (ZMod p) p (O p n a b J₁))
      (datum_V_pow_O_eq_zero p n a b hab J₁) (datum_F_pow_O_eq p n a b hab J₁) (fun κ => (κ : _))
  simp only [DieudonneModule.dieudonneDatum_F_apply, DieudonneModule.dieudonneDatum_V_apply] at hρ'F hρ'V

  have hρρ' : ∀ z, ρ (ρ' z) = 0 := by
    let N : AddSubgroup (DieudonneModule (ZMod p) p (O p n a b J₂)) := (ρ.comp ρ').ker
    have hN : N = ⊤ := by
      refine hgen₂ N (fun z hz => ?_) (fun z hz => ?_) (fun κ => ?_)
      · change ρ (ρ' _) = 0
        have hz' : ρ (ρ' z) = 0 := hz
        rw [hρ'F, hρF, hz', map_zero]
      · change ρ (ρ' _) = 0
        have hz' : ρ (ρ' z) = 0 := hz
        rw [hρ'V, hρV, hz', map_zero]
      · change ρ (ρ' _) = 0
        rw [hρ'τ]
        exact κ.2
    intro z
    have hz : z ∈ N := by rw [hN]; trivial
    exact hz
  have hrange : ρ'.range = ρ.ker := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      exact hρρ' z
    · intro w hw
      exact ⟨tautoClass (ZMod p) p n a b J₂ ⟨w, hw⟩, hρ'τ ⟨w, hw⟩⟩

  have hA₁ : IsLocalRing (CartierDual (ZMod p) (O p n a b J₁)) := isLocalRing_O p n a b J₁
  have hA₂ : IsLocalRing (CartierDual (ZMod p) (O p n a b J₂)) := isLocalRing_O p n a b J₂
  obtain ⟨g, hg⟩ :=
    (Deformation.DieudonneModule.map_injective_and_exists_map_eq_of_isLocalRing_cartierDual p
      (O p n a b J₁) (O p n a b J₂) hA₁ hA₂).2 ρ' hρ'F hρ'V

  let I : Ideal (O p n a b J₁) :=
    (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) (O p n a b J₂))).map
      (g : O p n a b J₂ →ₐ[ZMod p] O p n a b J₁)
  haveI hI : I.IsHopfIdeal' (ZMod p) := isHopfIdeal_map_ker_counit g
  let B : Type := O p n a b J₁ ⧸ I
  let q : O p n a b J₁ →ₐc[ZMod p] B := HopfAlgebra.quotientBialgHom (ZMod p) I
  have hq : Function.Surjective q := HopfAlgebra.quotientBialgHom_surjective (ZMod p) I
  haveI : Module.Finite (ZMod p) B :=
    Module.Finite.of_surjective ((q : O p n a b J₁ →ₐ[ZMod p] B).toLinearMap) hq
  have hkerq : RingHom.ker (q : O p n a b J₁ →ₐ[ZMod p] B) = I := Ideal.mk_ker

  obtain ⟨hMq, hexact⟩ :=
    Deformation.DieudonneModule.map_surjective_and_exact_map_of_ker_eq_map_ker_counit (ZMod p) p
      (O p n a b J₂) (O p n a b J₁) hA₂ hA₁ B g q hq hkerq
  have hB : IsLocalRing (CartierDual (ZMod p) B) :=
    HopfAlgebra.isLocalRing_cartierDual_of_surjective (ZMod p) (O p n a b J₁) B q hq hA₁

  have hker : (DieudonneModule.map (ZMod p) p q).ker = ρ.ker := by
    rw [hexact.addMonoidHom_ker_eq, hg, hrange]
  let e : DieudonneModule (ZMod p) p B ≃+ D :=
    equivOfSurjective (DieudonneModule.map (ZMod p) p q) ρ hMq hρsurj hker
  refine ⟨B, inferInstance, inferInstance, inferInstance, inferInstance, hB, e, ?_, ?_⟩
  · intro w
    obtain ⟨z, rfl⟩ := hMq w
    rw [← DieudonneModule.map_frobenius, equivOfSurjective_apply, equivOfSurjective_apply, hρF]
  · intro w
    obtain ⟨z, rfl⟩ := hMq w
    rw [← DieudonneModule.map_verschiebung, equivOfSurjective_apply, equivOfSurjective_apply, hρV]

end Main

end DieudonneFiniteZMod
p2m_reactivate "P2MW.S_Deformation_DieudonneDatum_exists_hopfAlgebra_zmod_addEquiv_dieudonneModule_of_isNilpotent.DieudonneFiniteZMod"

end
p2m_reactivate "P2MW.S_Deformation_DieudonneDatum_exists_hopfAlgebra_zmod_addEquiv_dieudonneModule_of_isNilpotent.DieudonneFiniteZMod"

theorem solution
    (p : ℕ) [Fact p.Prime]
    {D : Type u} [AddCommGroup D] [Finite D] (M : Deformation.DieudonneDatum (p : ℤ) D)
    (hV : IsNilpotent M.V) :
    ∃ (B : Type) (_ : CommRing B) (_ : HopfAlgebra (ZMod p) B) (_ : Coalgebra.IsCocomm (ZMod p) B)
      (_ : Module.Finite (ZMod p) B),
      IsLocalRing (CartierDual (ZMod p) B) ∧
      ∃ e : Deformation.DieudonneModule (ZMod p) p B ≃+ D,
        (∀ z, e (Deformation.DieudonneModule.frobenius (ZMod p) p B z) = M.F (e z)) ∧
        (∀ z, e (Deformation.DieudonneModule.verschiebung (ZMod p) p B z) = M.V (e z)) := by
  obtain ⟨n, hn⟩ := hV
  obtain ⟨a, b, hab, hFab⟩ := DieudonneFiniteZMod.exists_lt_pow_eq M.F
  exact DieudonneFiniteZMod.exists_realisation p M n a b hab hn hFab

end S_Deformation_DieudonneDatum_exists_hopfAlgebra_zmod_addEquiv_dieudonneModule_of_isNilpotent
end P2MW
export P2MW.S_Deformation_DieudonneDatum_exists_hopfAlgebra_zmod_addEquiv_dieudonneModule_of_isNilpotent (solution)
