-- Prove2me | solution 1 for CohCarrier.exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/ca903f1b-2bee-5b37-883d-fa9e79e44f5a

import Definitions.Def_CohCarrier_Inst
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_ModularCurve_PDPairing
import Theorems.Thm_ModularCurve_PDPairing_exists_forall_smul_eq_pairZ_and_perfect_mod_three
import Theorems.Thm_ModularCurve_PDPairing_pairZFun_jDeg0_iDeg0
import Theorems.Thm_ModularCurve_PDPairing_pairZ_nondegenerate_mod
import Theorems.Thm_ModularCurve_PDPairing_isFreeGroup_Gamma_four
import Theorems.Thm_ModularCurve_Period_exists_basis_parabolicHoms_of_isAddTorsionFree
import Theorems.Thm_ModularCurve_PDPairing_heckeT0_apply_eq_heckeT_top_apply
import Theorems.Thm_CohCarrier_isParabolicHom_heckeT_top
import Theorems.Thm_CohCarrier_jDegL_mem_parabolicHoms
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.LinearAlgebra.Basis.Bilinear
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.NatInt
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.Data.Int.GCD
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms
p2m_attr_erase "instance" "ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper"
p2m_attr_erase "simp" "HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero"

set_option autoImplicit false

namespace TransferNaturality

open scoped Pointwise

private theorem section_mul_mem {G : Type*} [Group G] (H : Subgroup G) (f : G ⧸ H → G)
    (hf : ∀ q, (f q : G ⧸ H) = q) (g : G) (q : G ⧸ H) : (f (g • q))⁻¹ * (g * f q) ∈ H := by
  refine QuotientGroup.eq.mp ?_
  rw [hf]
  show g • q = ((g * f q : G) : G ⧸ H)
  rw [show ((g * f q : G) : G ⧸ H) = g • ((f q : G) : G ⧸ H) from rfl, hf]

private theorem transfer_eq_prod_section {G : Type*} [Group G] (H : Subgroup G) [H.FiniteIndex]
    {A : Type*} [CommGroup A] (ϕ : ↥H →* A) (f : G ⧸ H → G) (hf : ∀ q, (f q : G ⧸ H) = q) (g : G) :
    MonoidHom.transfer ϕ g =
      (letI := H.fintypeQuotientOfFiniteIndex
       ∏ q : G ⧸ H, ϕ ⟨(f (g • q))⁻¹ * (g * f q), section_mul_mem H f hf g q⟩) := by
  letI := H.fintypeQuotientOfFiniteIndex
  let T : H.LeftTransversal := ⟨Set.range f, Subgroup.isComplement_range_left hf⟩
  rw [MonoidHom.transfer_def ϕ T g]
  simp only [Subgroup.leftTransversals.diff]
  refine (Fintype.prod_bijective (g • ·) (MulAction.bijective g) _ _ fun q => ?_).symm
  have hα : ∀ q : G ⧸ H, ((T.2.leftQuotientEquiv q : G)) = f q := fun q =>
    Subgroup.IsComplement.leftQuotientEquiv_apply hf q
  have hβ : (((g • T).2.leftQuotientEquiv (g • q) : G)) = g * f q := by
    rw [Subgroup.smul_apply_eq_smul_apply_inv_smul, inv_smul_smul, hα, smul_eq_mul]
  congr 1
  apply Subtype.ext
  show (f (g • q))⁻¹ * (g * f q) = ((T.2.leftQuotientEquiv (g • q) : G))⁻¹ * _
  rw [hα, hβ]

private def quotientCongr {G G' : Type*} [Group G] [Group G'] (H : Subgroup G) (H' : Subgroup G')
    (e : G ≃* G') (he : ∀ x, e x ∈ H' ↔ x ∈ H) : G ⧸ H ≃ G' ⧸ H' :=
  Quotient.congr e.toEquiv fun a b => by
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
    show a⁻¹ * b ∈ H ↔ (e a)⁻¹ * e b ∈ H'
    rw [← map_inv, ← map_mul, he]

private theorem quotientCongr_mk {G G' : Type*} [Group G] [Group G'] (H : Subgroup G) (H' : Subgroup G')
    (e : G ≃* G') (he : ∀ x, e x ∈ H' ↔ x ∈ H) (x : G) :
    quotientCongr H H' e he (x : G ⧸ H) = ((e x : G') : G' ⧸ H') := rfl

private theorem quotientCongr_smul {G G' : Type*} [Group G] [Group G'] (H : Subgroup G) (H' : Subgroup G')
    (e : G ≃* G') (he : ∀ x, e x ∈ H' ↔ x ∈ H) (g : G) (q : G ⧸ H) :
    quotientCongr H H' e he (g • q) = e g • quotientCongr H H' e he q := by
  induction q using QuotientGroup.induction_on with
  | H x =>
    show quotientCongr H H' e he ((g * x : G) : G ⧸ H) = e g • ((e x : G') : G' ⧸ H')
    rw [quotientCongr_mk, map_mul]
    rfl

private def pairRestrict {G G' : Type*} [Group G] [Group G'] (H : Subgroup G) (H' : Subgroup G')
    (e : G ≃* G') (he : ∀ x, e x ∈ H' ↔ x ∈ H) : ↥H →* ↥H' :=
  (e.toMonoidHom.comp H.subtype).codRestrict H' fun h => (he h).mpr h.2

@[scoped simp] private theorem coe_pairRestrict_apply {G G' : Type*} [Group G] [Group G'] (H : Subgroup G)
    (H' : Subgroup G') (e : G ≃* G') (he : ∀ x, e x ∈ H' ↔ x ∈ H) (h : ↥H) :
    ((pairRestrict H H' e he h : ↥H') : G') = e h := rfl

private theorem transfer_comp_restrict {G G' : Type*} [Group G] [Group G'] (H : Subgroup G) (H' : Subgroup G')
    [H.FiniteIndex] [H'.FiniteIndex] (e : G ≃* G') (he : ∀ x, e x ∈ H' ↔ x ∈ H)
    {A : Type*} [CommGroup A] (ψ' : ↥H' →* A) (g : G) :
    MonoidHom.transfer (ψ'.comp (pairRestrict H H' e he)) g = MonoidHom.transfer ψ' (e g) := by
  letI := H.fintypeQuotientOfFiniteIndex
  letI := H'.fintypeQuotientOfFiniteIndex

  have hf : ∀ q : G ⧸ H, ((Quotient.out q : G) : G ⧸ H) = q := QuotientGroup.out_eq'
  have hf' : ∀ q' : G' ⧸ H',
      ((e (Quotient.out ((quotientCongr H H' e he).symm q')) : G') : G' ⧸ H') = q' := fun q' => by
    obtain ⟨q, rfl⟩ := (quotientCongr H H' e he).surjective q'
    rw [(quotientCongr H H' e he).symm_apply_apply]
    show quotientCongr H H' e he ((Quotient.out q : G) : G ⧸ H) = quotientCongr H H' e he q
    rw [hf]
  rw [transfer_eq_prod_section H (ψ'.comp (pairRestrict H H' e he)) Quotient.out hf g,
    transfer_eq_prod_section H' ψ' (fun q' => e (Quotient.out ((quotientCongr H H' e he).symm q'))) hf'
      (e g)]
  refine Fintype.prod_equiv (quotientCongr H H' e he) _ _ fun q => ?_
  have key : (e (Quotient.out (g • q)))⁻¹ * (e g * e (Quotient.out q)) =
      (e (Quotient.out ((quotientCongr H H' e he).symm (e g • quotientCongr H H' e he q))))⁻¹ *
        (e g * e (Quotient.out ((quotientCongr H H' e he).symm (quotientCongr H H' e he q)))) := by
    rw [← quotientCongr_smul H H' e he, (quotientCongr H H' e he).symm_apply_apply,
      (quotientCongr H H' e he).symm_apply_apply]
  rw [MonoidHom.comp_apply]
  congr 1
  apply Subtype.ext
  rw [coe_pairRestrict_apply, map_mul, map_mul, map_inv]
  exact key

private theorem cores_push_natural {G G' K K' : Type*} [Group G] [Group G'] [Group K] [Group K']
    (e : G ≃* G') (ek : K ≃* K') (ι : K →* G) (ι' : K' →* G')
    (hι : Function.Injective ι) (hι' : Function.Injective ι') (hsq : ∀ k, e (ι k) = ι' (ek k))
    [ι.range.FiniteIndex] [ι'.range.FiniteIndex] {A : Type*} [AddCommGroup A] (φ' : Additive K' →+ A) (g : G) :
    MonoidHom.toAdditiveLeft (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight
        ((φ'.comp (MonoidHom.toAdditive ek.toMonoidHom)).comp
          (MonoidHom.toAdditive (MonoidHom.ofInjective hι).symm.toMonoidHom)))) (Additive.ofMul g) =
      MonoidHom.toAdditiveLeft (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight
        (φ'.comp (MonoidHom.toAdditive (MonoidHom.ofInjective hι').symm.toMonoidHom)))) (Additive.ofMul (e g)) := by
  have he : ∀ x, e x ∈ ι'.range ↔ x ∈ ι.range := fun x => by
    constructor
    · rintro ⟨k', hk'⟩
      refine ⟨ek.symm k', e.injective ?_⟩
      rw [hsq, MulEquiv.apply_symm_apply, hk']
    · rintro ⟨k, rfl⟩
      exact ⟨ek k, (hsq k).symm⟩
  have hψ : (AddMonoidHom.toMultiplicativeRight
        (φ'.comp (MonoidHom.toAdditive (MonoidHom.ofInjective hι').symm.toMonoidHom))).comp
        (pairRestrict ι.range ι'.range e he) =
      AddMonoidHom.toMultiplicativeRight ((φ'.comp (MonoidHom.toAdditive ek.toMonoidHom)).comp
        (MonoidHom.toAdditive (MonoidHom.ofInjective hι).symm.toMonoidHom)) := by
    refine MonoidHom.ext fun x => ?_
    obtain ⟨k, hk⟩ : ∃ k, ι k = (x : G) := x.2
    have hx : x = MonoidHom.ofInjective hι k := Subtype.ext (by rw [MonoidHom.ofInjective_apply, hk])
    have hx' : pairRestrict ι.range ι'.range e he x = MonoidHom.ofInjective hι' (ek k) :=
      Subtype.ext (by rw [coe_pairRestrict_apply, MonoidHom.ofInjective_apply, ← hsq, hk])
    show Multiplicative.ofAdd (φ' (Additive.ofMul ((MonoidHom.ofInjective hι').symm
        (pairRestrict ι.range ι'.range e he x)))) =
      Multiplicative.ofAdd (φ' (Additive.ofMul (ek ((MonoidHom.ofInjective hι).symm x))))
    rw [hx', MulEquiv.symm_apply_apply, hx, MulEquiv.symm_apply_apply]
  show Multiplicative.toAdd (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight
        ((φ'.comp (MonoidHom.toAdditive ek.toMonoidHom)).comp
          (MonoidHom.toAdditive (MonoidHom.ofInjective hι).symm.toMonoidHom))) g) =
    Multiplicative.toAdd (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight
        (φ'.comp (MonoidHom.toAdditive (MonoidHom.ofInjective hι').symm.toMonoidHom))) (e g))
  rw [← hψ, transfer_comp_restrict]

end TransferNaturality
p2m_reactivate "P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.TransferNaturality"

namespace MatrixTransfer

variable {𝒪 : Type*} [CommRing 𝒪]
variable {Vz VO Vz' VO' : Type*} [AddCommGroup Vz] [AddCommGroup VO] [Module 𝒪 VO]
  [AddCommGroup Vz'] [AddCommGroup VO'] [Module 𝒪 VO']
variable {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

private noncomputable def castForm (bZ : Module.Basis ι ℤ Vz) (bO : Module.Basis ι 𝒪 VO)
    (Bz : Vz →ₗ[ℤ] Vz →ₗ[ℤ] ℤ) : VO →ₗ[𝒪] VO →ₗ[𝒪] 𝒪 :=
  Matrix.toLinearMap₂ bO bO ((LinearMap.toMatrix₂ bZ bZ Bz).map (Int.castRingHom 𝒪))

private theorem castForm_basis (bZ : Module.Basis ι ℤ Vz) (bO : Module.Basis ι 𝒪 VO) (Bz : Vz →ₗ[ℤ] Vz →ₗ[ℤ] ℤ)
    (i j : ι) : castForm bZ bO Bz (bO i) (bO j) = ((Bz (bZ i) (bZ j) : ℤ) : 𝒪) := by
  rw [castForm, Matrix.toLinearMap₂_apply_basis, Matrix.map_apply, LinearMap.toMatrix₂_apply, eq_intCast]

private theorem castForm_apply_cast (bZ : Module.Basis ι ℤ Vz) (bO : Module.Basis ι 𝒪 VO)
    (Bz : Vz →ₗ[ℤ] Vz →ₗ[ℤ] ℤ) (κ : Vz →+ VO) (hκ : ∀ i, bO i = κ (bZ i)) (x y : Vz) :
    castForm bZ bO Bz (κ x) (κ y) = ((Bz x y : ℤ) : 𝒪) := by
  let F₁ : Vz →ₗ[ℤ] Vz →ₗ[ℤ] 𝒪 :=
    ((castForm bZ bO Bz).restrictScalars₁₂ ℤ ℤ).compl₁₂ κ.toIntLinearMap κ.toIntLinearMap
  let F₂ : Vz →ₗ[ℤ] Vz →ₗ[ℤ] 𝒪 := Bz.compr₂ (Int.castAddHom 𝒪).toIntLinearMap
  have hF : F₁ = F₂ := LinearMap.ext_basis bZ bZ fun i j => by
    show castForm bZ bO Bz (κ (bZ i)) (κ (bZ j)) = ((Bz (bZ i) (bZ j) : ℤ) : 𝒪)
    rw [← hκ, ← hκ, castForm_basis]
  exact LinearMap.congr_fun₂ hF x y

private theorem castForm_comm (bZ : Module.Basis ι ℤ Vz) (bO : Module.Basis ι 𝒪 VO) (Bz : Vz →ₗ[ℤ] Vz →ₗ[ℤ] ℤ)
    (κ : Vz →+ VO) (hκ : ∀ i, bO i = κ (bZ i)) (Tz : Vz →ₗ[ℤ] Vz) (TO : VO →ₗ[𝒪] VO)
    (hT : ∀ x, TO (κ x) = κ (Tz x)) (hadj : ∀ x y, Bz (Tz x) y = Bz x (Tz y)) (X Y : VO) :
    castForm bZ bO Bz (TO X) Y = castForm bZ bO Bz X (TO Y) := by
  have hF : (castForm bZ bO Bz).comp TO = (castForm bZ bO Bz).compl₂ TO :=
    LinearMap.ext_basis bO bO fun i j => by
      show castForm bZ bO Bz (TO (bO i)) (bO j) = castForm bZ bO Bz (bO i) (TO (bO j))
      rw [hκ i, hκ j, hT, hT, castForm_apply_cast bZ bO Bz κ hκ, castForm_apply_cast bZ bO Bz κ hκ, hadj]
  exact LinearMap.congr_fun₂ hF X Y

private theorem castForm_adjoint (bZ : Module.Basis ι ℤ Vz) (bO : Module.Basis ι 𝒪 VO) (Bz : Vz →ₗ[ℤ] Vz →ₗ[ℤ] ℤ)
    (κ : Vz →+ VO) (hκ : ∀ i, bO i = κ (bZ i))
    (bZ' : Module.Basis ι' ℤ Vz') (bO' : Module.Basis ι' 𝒪 VO') (Bz' : Vz' →ₗ[ℤ] Vz' →ₗ[ℤ] ℤ)
    (κ' : Vz' →+ VO') (hκ' : ∀ i, bO' i = κ' (bZ' i))
    (iz : Vz →ₗ[ℤ] Vz') (iO : VO →ₗ[𝒪] VO') (hi : ∀ x, iO (κ x) = κ' (iz x))
    (jz : Vz' →ₗ[ℤ] Vz) (jO : VO' →ₗ[𝒪] VO) (hj : ∀ y', jO (κ' y') = κ (jz y'))
    (hadj : ∀ (x : Vz) (y' : Vz'), Bz (jz y') x = Bz' y' (iz x)) (X : VO) (Y' : VO') :
    castForm bZ bO Bz (jO Y') X = castForm bZ' bO' Bz' Y' (iO X) := by
  have hF : (castForm bZ bO Bz).comp jO = (castForm bZ' bO' Bz').compl₂ iO :=
    LinearMap.ext_basis bO' bO fun i j => by
      show castForm bZ bO Bz (jO (bO' i)) (bO j) = castForm bZ' bO' Bz' (bO' i) (iO (bO j))
      rw [hκ' i, hκ j, hj, hi, castForm_apply_cast bZ bO Bz κ hκ, castForm_apply_cast bZ' bO' Bz' κ' hκ', hadj]
  exact LinearMap.congr_fun₂ hF Y' X

end MatrixTransfer
p2m_reactivate "P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.TransferNaturality"

namespace CohCarrier
p2m_export "CohCarrier" "heckeTL gamma0Units_surjective diamondL diamondL_eq_diamondRaw coresAdd mem_Gamma0Upper GammaH mem_GammaH_iff GammaH_le_Gamma0 GammaH_top H1 conjUpperMat conjUpperMat_apply_10 conjL heckeT conjHom conjLowerMat LevelLE iotaDeg iDeg' iDegL conjLowerMat_conjUpperMat iotaDeg_injective pushChar jDeg jDegL isParabolicHom_heckeT_top jDegL_mem_parabolicHoms"
namespace ParabolicDuality
p2m_open "CohCarrier"

open CongruenceSubgroup ModularCurve.Period
open scoped MatrixGroups

section Transport

variable (M : ℕ)

private def topIso : ↥(GammaH M ⊤) ≃* ↥(Gamma0 M) := MulEquiv.subgroupCongr (GammaH_top (M := M))

@[scoped simp] private theorem coe_topIso (γ : ↥(GammaH M ⊤)) : ((topIso M γ : ↥(Gamma0 M)) : SL(2, ℤ)) = γ := rfl

@[scoped simp] private theorem coe_topIso_symm (γ : ↥(Gamma0 M)) : (((topIso M).symm γ : ↥(GammaH M ⊤)) : SL(2, ℤ)) = γ :=
  rfl

variable (A : Type*) [AddCommGroup A]

private def toTop : (Additive ↥(Gamma0 M) →+ A) →+ H1 M ⊤ A where
  toFun ψ := ψ.comp (MonoidHom.toAdditive (topIso M).toMonoidHom)
  map_zero' := by ext; rfl
  map_add' := by intro φ ψ; ext; rfl

private def ofTop : H1 M ⊤ A →+ (Additive ↥(Gamma0 M) →+ A) where
  toFun φ := φ.comp (MonoidHom.toAdditive (topIso M).symm.toMonoidHom)
  map_zero' := by ext; rfl
  map_add' := by intro φ ψ; ext; rfl

private theorem toTop_apply (ψ : Additive ↥(Gamma0 M) →+ A) (γ : ↥(GammaH M ⊤)) :
    toTop M A ψ (Additive.ofMul γ) = ψ (Additive.ofMul (topIso M γ)) := rfl

private theorem ofTop_apply (φ : H1 M ⊤ A) (γ : ↥(Gamma0 M)) :
    ofTop M A φ (Additive.ofMul γ) = φ (Additive.ofMul ((topIso M).symm γ)) := rfl

@[scoped simp] private theorem ofTop_toTop (ψ : Additive ↥(Gamma0 M) →+ A) : ofTop M A (toTop M A ψ) = ψ := by
  refine AddMonoidHom.ext fun x => ?_
  show ψ (Additive.ofMul (topIso M ((topIso M).symm (Additive.toMul x)))) = ψ x
  rw [MulEquiv.apply_symm_apply]
  rfl

@[scoped simp] private theorem toTop_ofTop (φ : H1 M ⊤ A) : toTop M A (ofTop M A φ) = φ := by
  refine AddMonoidHom.ext fun x => ?_
  show φ (Additive.ofMul ((topIso M).symm (topIso M (Additive.toMul x)))) = φ x
  rw [MulEquiv.symm_apply_apply]
  rfl

private theorem ofTop_agree (φ : H1 M ⊤ A) (γ : ↥(GammaH M ⊤)) :
    φ (Additive.ofMul γ) = ofTop M A φ (Additive.ofMul ⟨(γ : SL(2, ℤ)), GammaH_le_Gamma0 ⊤ γ.2⟩) := by
  rw [ofTop_apply]
  congr 2

private theorem isParabolicHom_toTop {ψ : Additive ↥(Gamma0 M) →+ A} (hψ : IsParabolicHom (Gamma0 M) ψ) :
    IsParabolicHom (GammaH M ⊤) (toTop M A ψ) := fun γ hγ => by
  rw [toTop_apply]
  exact hψ _ hγ

private theorem isParabolicHom_ofTop {φ : H1 M ⊤ A} (hφ : IsParabolicHom (GammaH M ⊤) φ) :
    IsParabolicHom (Gamma0 M) (ofTop M A φ) := fun γ hγ => by
  rw [ofTop_apply]
  exact hφ _ hγ

private def mapCoeff {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) {Γ : Type*} [Group Γ] :
    (Additive Γ →+ A) →+ (Additive Γ →+ B) where
  toFun φ := f.comp φ
  map_zero' := by ext; simp
  map_add' := by intro φ ψ; ext; simp

private theorem mapCoeff_apply {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) {Γ : Type*} [Group Γ]
    (φ : Additive Γ →+ A) (x : Additive Γ) : mapCoeff f φ x = f (φ x) := rfl

private theorem isParabolicHom_mapCoeff {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B)
    {Γ : Subgroup SL(2, ℤ)} {φ : Additive ↥Γ →+ A} (hφ : IsParabolicHom Γ φ) :
    IsParabolicHom Γ (mapCoeff f φ) := fun γ hγ => by
  rw [mapCoeff_apply, hφ γ hγ, map_zero]

end Transport
p2m_reactivate "P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.TransferNaturality"

section CoeffNaturality

private theorem transfer_comp_left {G : Type*} [Group G] (K : Subgroup G) [K.FiniteIndex] {A B : Type*} [CommGroup A]
    [CommGroup B] (F : A →* B) (ϕ : ↥K →* A) (g : G) :
    MonoidHom.transfer (F.comp ϕ) g = F (MonoidHom.transfer ϕ g) := by
  rw [MonoidHom.transfer_def (F.comp ϕ) default g, MonoidHom.transfer_def ϕ default g]
  simp only [Subgroup.leftTransversals.diff, map_prod, MonoidHom.coe_comp, Function.comp_apply]

private theorem coresAdd_mapCoeff {G : Type*} [Group G] (K : Subgroup G) [K.FiniteIndex] {A B : Type*}
    [AddCommGroup A] [AddCommGroup B] (f : A →+ B) (φ : Additive ↥K →+ A) :
    coresAdd K (mapCoeff f φ) = mapCoeff f (coresAdd K φ) := by
  ext g
  show MonoidHom.toAdditiveLeft (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight (f.comp φ))) g =
    f (MonoidHom.toAdditiveLeft (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight φ)) g)
  have hcomp : AddMonoidHom.toMultiplicativeRight (f.comp φ) =
      (AddMonoidHom.toMultiplicative f).comp (AddMonoidHom.toMultiplicativeRight φ) := by
    ext; rfl
  rw [hcomp]
  show Multiplicative.toAdd (MonoidHom.transfer
      ((AddMonoidHom.toMultiplicative f).comp (AddMonoidHom.toMultiplicativeRight φ)) (Additive.toMul g)) =
    f (Multiplicative.toAdd (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight φ) (Additive.toMul g)))
  rw [transfer_comp_left]
  rfl

variable (M M' : ℕ) (d ℓ : ℕ)

private theorem heckeT_mapCoeff {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) [NeZero ℓ]
    (φ : H1 M ⊤ A) : heckeT M ⊤ ℓ B (mapCoeff f φ) = mapCoeff f (heckeT M ⊤ ℓ A φ) := by
  ext g
  show MonoidHom.toAdditiveLeft (MonoidHom.transfer
      ((AddMonoidHom.toMultiplicativeRight (f.comp φ)).comp (conjL M ⊤ ℓ))) g =
    f (MonoidHom.toAdditiveLeft (MonoidHom.transfer
      ((AddMonoidHom.toMultiplicativeRight φ).comp (conjL M ⊤ ℓ))) g)
  have hcomp : (AddMonoidHom.toMultiplicativeRight (f.comp φ)).comp (conjL M ⊤ ℓ) =
      (AddMonoidHom.toMultiplicative f).comp ((AddMonoidHom.toMultiplicativeRight φ).comp (conjL M ⊤ ℓ)) := by
    ext; rfl
  rw [hcomp]
  show Multiplicative.toAdd (MonoidHom.transfer ((AddMonoidHom.toMultiplicative f).comp
      ((AddMonoidHom.toMultiplicativeRight φ).comp (conjL M ⊤ ℓ))) (Additive.toMul g)) =
    f (Multiplicative.toAdd (MonoidHom.transfer
      ((AddMonoidHom.toMultiplicativeRight φ).comp (conjL M ⊤ ℓ)) (Additive.toMul g)))
  rw [transfer_comp_left]
  rfl

private theorem iDegL_mapCoeff {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) [NeZero d]
    (h : LevelLE M M' ⊤ ⊤ d) (φ : H1 M ⊤ A) :
    iDegL M M' ⊤ ⊤ d B ℤ h (mapCoeff f φ) = mapCoeff f (iDegL M M' ⊤ ⊤ d A ℤ h φ) := rfl

private theorem jDegL_mapCoeff {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) [NeZero M'] [NeZero d]
    (h : LevelLE M M' ⊤ ⊤ d) (φ : H1 M' ⊤ A) :
    jDegL M M' ⊤ ⊤ d B ℤ h (mapCoeff f φ) = mapCoeff f (jDegL M M' ⊤ ⊤ d A ℤ h φ) := by
  have hpush : pushChar M M' ⊤ ⊤ d B h (mapCoeff f φ) = mapCoeff f (pushChar M M' ⊤ ⊤ d A h φ) := by
    ext; rfl
  show coresAdd _ (pushChar M M' ⊤ ⊤ d B h (mapCoeff f φ)) = mapCoeff f (coresAdd _ (pushChar M M' ⊤ ⊤ d A h φ))
  rw [hpush, coresAdd_mapCoeff]

end CoeffNaturality
p2m_reactivate "P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.TransferNaturality"

section Diamond

variable (M : ℕ) (𝒪 : Type) [CommRing 𝒪]

private theorem diamondL_top_apply [NeZero M] (d : (ZMod M)ˣ) (φ : H1 M ⊤ 𝒪) : diamondL M ⊤ 𝒪 d φ = φ := by
  set σ := Classical.choose (gamma0Units_surjective M d) with hσ
  have hmem : (σ : SL(2, ℤ)) ∈ GammaH M ⊤ := by
    rw [GammaH_top]
    exact σ.2
  rw [diamondL_eq_diamondRaw M ⊤ 𝒪 d σ (Classical.choose_spec (gamma0Units_surjective M d))]
  ext γ
  show φ (Additive.ofMul (conjHom M ⊤ σ γ)) = φ (Additive.ofMul γ)
  have hconj : conjHom M ⊤ σ γ = ⟨σ, hmem⟩ * γ * ⟨σ, hmem⟩⁻¹ := Subtype.ext rfl
  rw [hconj, ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg]
  abel

end Diamond
p2m_reactivate "P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.TransferNaturality"

end CohCarrier.ParabolicDuality
p2m_reactivate "P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.TransferNaturality P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier.ParabolicDuality"
p2m_reactivate "P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.TransferNaturality P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier"

namespace CohCarrier
p2m_export "CohCarrier" "heckeTL gamma0Units_surjective diamondL diamondL_eq_diamondRaw coresAdd mem_Gamma0Upper GammaH mem_GammaH_iff GammaH_le_Gamma0 GammaH_top H1 conjUpperMat conjUpperMat_apply_10 conjL heckeT conjHom conjLowerMat LevelLE iotaDeg iDeg' iDegL conjLowerMat_conjUpperMat iotaDeg_injective pushChar jDeg jDegL isParabolicHom_heckeT_top jDegL_mem_parabolicHoms"
p2m_open "CohCarrier"

open Matrix CongruenceSubgroup
open scoped MatrixGroups

section AtkinLehner

variable (M : ℕ)

private def wMat (γ : SL(2, ℤ)) (h : (M : ℤ) ∣ γ 1 0) : SL(2, ℤ) :=
  ⟨!![γ 1 1, -(γ 1 0 / M); -(γ 0 1 * M), γ 0 0], by
    rw [Matrix.det_fin_two_of]
    have hdet := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at hdet
    have hcM : γ 1 0 / M * M = γ 1 0 := Int.ediv_mul_cancel h
    linear_combination hdet - γ 0 1 * hcM⟩

private theorem dvd_entry_of_mem (γ : ↥(GammaH M ⊤)) : (M : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 := by
  obtain ⟨hγ0, _⟩ := mem_GammaH_iff.mp γ.2
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ0)

private theorem wMat_mem (γ : ↥(GammaH M ⊤)) : wMat M (γ : SL(2, ℤ)) (dvd_entry_of_mem M γ) ∈ GammaH M ⊤ := by
  rw [mem_GammaH_iff]
  refine ⟨?_, Subgroup.mem_top _⟩
  rw [Gamma0_mem]
  show (((!![(γ : SL(2, ℤ)) 1 1, -((γ : SL(2, ℤ)) 1 0 / M); -((γ : SL(2, ℤ)) 0 1 * M), (γ : SL(2, ℤ)) 0 0]
    : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod M) = 0
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  push_cast
  rw [ZMod.natCast_self, mul_zero, neg_zero]

private theorem wMat_mul (γ δ : SL(2, ℤ)) (hγ : (M : ℤ) ∣ γ 1 0) (hδ : (M : ℤ) ∣ δ 1 0)
    (hγδ : (M : ℤ) ∣ (γ * δ) 1 0) : wMat M (γ * δ) hγδ = wMat M γ hγ * wMat M δ hδ := by
  have hmul : ∀ i j, (γ * δ) i j = γ i 0 * δ 0 j + γ i 1 * δ 1 j := fun i j => by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have h2 : (γ 1 0 * δ 0 0 + γ 1 1 * δ 1 0) / M = γ 1 0 / M * δ 0 0 + γ 1 1 * (δ 1 0 / M) := by
    rw [Int.add_ediv_of_dvd_right (Dvd.dvd.mul_left hδ _), Int.mul_ediv_assoc _ hδ,
      mul_comm (γ 1 0) (δ 0 0), Int.mul_ediv_assoc _ hγ, mul_comm (δ 0 0)]
  have hc : γ 1 0 / M * M = γ 1 0 := Int.ediv_mul_cancel hγ
  have hc' : M * (δ 1 0 / M) = δ 1 0 := Int.mul_ediv_cancel' hδ
  have hcB : ∀ x : ℤ, x * M * (δ 1 0 / M) = x * δ 1 0 := fun x => by rw [mul_assoc, hc']
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [wMat, Matrix.mul_apply, Fin.sum_univ_two, hmul, h2, hcB]
  all_goals first | ring1 | (linear_combination (-(δ 0 1)) * hc)

private def wConj : ↥(GammaH M ⊤) →* ↥(GammaH M ⊤) where
  toFun γ := ⟨wMat M (γ : SL(2, ℤ)) (dvd_entry_of_mem M γ), wMat_mem M γ⟩
  map_one' := by
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [wMat]
  map_mul' γ δ :=
    Subtype.ext (wMat_mul M (γ : SL(2, ℤ)) (δ : SL(2, ℤ)) (dvd_entry_of_mem M γ) (dvd_entry_of_mem M δ)
      (dvd_entry_of_mem M (γ * δ)))

private theorem coe_wConj_apply (γ : ↥(GammaH M ⊤)) (i j : Fin 2) :
    ((wConj M γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j =
      (!![(γ : SL(2, ℤ)) 1 1, -((γ : SL(2, ℤ)) 1 0 / M); -((γ : SL(2, ℤ)) 0 1 * M), (γ : SL(2, ℤ)) 0 0]
        : Matrix (Fin 2) (Fin 2) ℤ) i j := rfl

private theorem trace_wConj (γ : ↥(GammaH M ⊤)) :
    ((wConj M γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace := by
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two, coe_wConj_apply, coe_wConj_apply]
  simp [add_comm]

private theorem wConj_wConj [NeZero M] (γ : ↥(GammaH M ⊤)) : wConj M (wConj M γ) = γ := by
  have hM0 : (M : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hc : (γ : SL(2, ℤ)) 1 0 / M * M = (γ : SL(2, ℤ)) 1 0 := Int.ediv_mul_cancel (dvd_entry_of_mem M γ)
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have hb : -((γ : SL(2, ℤ)) 0 1 * M) / (M : ℤ) = -((γ : SL(2, ℤ)) 0 1) := by
    rw [← neg_mul]
    exact Int.mul_ediv_cancel _ hM0
  fin_cases i <;> fin_cases j <;> simp [coe_wConj_apply, hb, hc]

variable (A : Type*) [AddCommGroup A]

private def wChar : H1 M ⊤ A →+ H1 M ⊤ A where
  toFun φ := φ.comp (MonoidHom.toAdditive (wConj M))
  map_zero' := by ext; rfl
  map_add' := by intro φ ψ; ext; rfl

private def wCharL (R : Type*) [Semiring R] [Module R A] : H1 M ⊤ A →ₗ[R] H1 M ⊤ A where
  toFun φ := φ.comp (MonoidHom.toAdditive (wConj M))
  map_add' := by intro φ ψ; ext; rfl
  map_smul' := by intro r φ; ext; rfl

private theorem wChar_apply (φ : H1 M ⊤ A) (γ : ↥(GammaH M ⊤)) :
    wChar M A φ (Additive.ofMul γ) = φ (Additive.ofMul (wConj M γ)) := rfl

private theorem wCharL_apply (R : Type*) [Semiring R] [Module R A] (φ : H1 M ⊤ A) :
    wCharL M A R φ = wChar M A φ := rfl

private theorem wChar_comp {B : Type*} [AddCommGroup B] (f : A →+ B) (φ : H1 M ⊤ A) :
    wChar M B (f.comp φ) = f.comp (wChar M A φ) := rfl

private theorem isParabolicHom_wChar (φ : H1 M ⊤ A)
    (hφ : ModularCurve.Period.IsParabolicHom (GammaH M ⊤) φ) :
    ModularCurve.Period.IsParabolicHom (GammaH M ⊤) (wChar M A φ) := by
  intro γ hγ
  rw [wChar_apply]
  exact hφ (wConj M γ) (by rw [trace_wConj]; exact hγ)

private theorem wChar_mem_parabolicHoms (R : Type*) [Semiring R] [Module R A] (φ : H1 M ⊤ A)
    (hφ : φ ∈ ModularCurve.Period.parabolicHoms R (GammaH M ⊤) A) :
    wChar M A φ ∈ ModularCurve.Period.parabolicHoms R (GammaH M ⊤) A :=
  isParabolicHom_wChar M A φ hφ

private theorem wChar_wChar [NeZero M] (φ : H1 M ⊤ A) : wChar M A (wChar M A φ) = φ := by
  ext γ
  show φ (Additive.ofMul (wConj M (wConj M (Additive.toMul γ)))) = φ γ
  rw [wConj_wConj]
  rfl

end AtkinLehner
p2m_reactivate "P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.TransferNaturality P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier.ParabolicDuality"

section Twist

variable (M M' : ℕ) (d d' : ℕ) [NeZero d] [NeZero d']

private theorem wConj_iotaDeg (h : LevelLE M M' ⊤ ⊤ d) (h' : LevelLE M M' ⊤ ⊤ d') (hdd' : d * d' = M' / M)
    (γ : ↥(GammaH M' ⊤)) :
    wConj M (iotaDeg M M' ⊤ ⊤ d h γ) = iotaDeg M M' ⊤ ⊤ d' h' (wConj M' γ) := by
  have hM' : (M' : ℤ) = M * (d * d') := by
    have := Nat.mul_div_cancel' h.dvd
    rw [← hdd'] at this
    exact_mod_cast this.symm
  obtain ⟨t, ht⟩ := dvd_entry_of_mem M' γ
  have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hd'0 : (d' : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne d'
  have hM'0 : (M' : ℤ) ≠ 0 := by
    have hne : M' ≠ 0 := by
      intro hz
      rw [hz, Nat.zero_div] at hdd'
      rcases Nat.mul_eq_zero.mp hdd' with h0 | h0
      · exact NeZero.ne d h0
      · exact NeZero.ne d' h0
    exact_mod_cast hne

  have e_cd : (γ : SL(2, ℤ)) 1 0 / d = M * d' * t := by
    apply Int.ediv_eq_of_eq_mul_right hd0
    rw [ht, hM']
    ring
  have e_cdM : M * d' * t / (M : ℤ) = d' * t := by
    have hM0 : (M : ℤ) ≠ 0 := fun hz => hM'0 (by rw [hM', hz, zero_mul])
    apply Int.ediv_eq_of_eq_mul_right hM0
    ring
  have e_cM' : (γ : SL(2, ℤ)) 1 0 / M' = t := by
    apply Int.ediv_eq_of_eq_mul_right hM'0
    exact ht
  have e_b : -((γ : SL(2, ℤ)) 0 1 * M') / (d' : ℤ) = -((γ : SL(2, ℤ)) 0 1 * d * M) := by
    apply Int.ediv_eq_of_eq_mul_right hd'0
    rw [hM']
    ring
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [iotaDeg, conjLowerMat, coe_wConj_apply, e_cd, e_cdM, e_cM', e_b]
  all_goals ring

private theorem wConj_comp_iotaDeg (h : LevelLE M M' ⊤ ⊤ d) (h' : LevelLE M M' ⊤ ⊤ d') (hdd' : d * d' = M' / M) :
    (wConj M).comp (iotaDeg M M' ⊤ ⊤ d h) = (iotaDeg M M' ⊤ ⊤ d' h').comp (wConj M') :=
  MonoidHom.ext (wConj_iotaDeg M M' d d' h h' hdd')

private theorem map_range_iotaDeg_wConj [NeZero M'] (h : LevelLE M M' ⊤ ⊤ d) (h' : LevelLE M M' ⊤ ⊤ d')
    (hdd' : d * d' = M' / M) :
    (iotaDeg M M' ⊤ ⊤ d h).range.map (wConj M) = (iotaDeg M M' ⊤ ⊤ d' h').range := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨γ, rfl⟩, rfl⟩
    exact ⟨wConj M' γ, (wConj_iotaDeg M M' d d' h h' hdd' γ).symm⟩
  · rintro _ ⟨γ, rfl⟩
    refine ⟨iotaDeg M M' ⊤ ⊤ d h (wConj M' γ), ⟨wConj M' γ, rfl⟩, ?_⟩
    rw [wConj_iotaDeg M M' d d' h h' hdd', wConj_wConj]

variable (A : Type*) [AddCommGroup A]

private theorem iDeg'_wChar (h : LevelLE M M' ⊤ ⊤ d) (h' : LevelLE M M' ⊤ ⊤ d') (hdd' : d * d' = M' / M)
    (φ : H1 M ⊤ A) :
    iDeg' M M' ⊤ ⊤ d A h (wChar M A φ) = wChar M' A (iDeg' M M' ⊤ ⊤ d' A h' φ) := by
  ext γ
  show φ (Additive.ofMul (wConj M (iotaDeg M M' ⊤ ⊤ d h (Additive.toMul γ)))) =
    φ (Additive.ofMul (iotaDeg M M' ⊤ ⊤ d' h' (wConj M' (Additive.toMul γ))))
  rw [wConj_iotaDeg M M' d d' h h' hdd']

private theorem iDegL_wCharL (R : Type*) [Semiring R] [Module R A] (h : LevelLE M M' ⊤ ⊤ d)
    (h' : LevelLE M M' ⊤ ⊤ d') (hdd' : d * d' = M' / M) (φ : H1 M ⊤ A) :
    iDegL M M' ⊤ ⊤ d A R h (wCharL M A R φ) = wCharL M' A R (iDegL M M' ⊤ ⊤ d' A R h' φ) :=
  iDeg'_wChar M M' d d' A h h' hdd' φ

end Twist
p2m_reactivate "P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.TransferNaturality P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier.ParabolicDuality"

end CohCarrier
p2m_reactivate "P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.TransferNaturality P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier.ParabolicDuality"

namespace ModularCurve
p2m_export "ModularCurve" "Period.IsParabolicHom Period.parabolicHoms PDPairing.pairZFun_jDeg0_iDeg0 PDPairing.isFreeGroup_Gamma_four"
namespace PDPairing
p2m_export "ModularCurve.PDPairing" "coresAdd conjUpperMat conjUpperMat_apply_10 conjLowerMat conjLowerMat_conjUpperMat dvd_entry0 iotaDeg0 iDeg0 iotaDeg0_injective pushChar0 jDeg0 mem_Gamma0Upper Gamma0HUpper dvd_of_mem_Gamma0HUpper conjL0 heckeT0 heckeT0_apply omega pairZFun pairZFun_swap pairZ exists_forall_smul_eq_pairZ_and_perfect_mod_three pairZFun_jDeg0_iDeg0 pairZ_nondegenerate_mod isFreeGroup_Gamma_four heckeT0_apply_eq_heckeT_top_apply"
namespace HeckeTranspose
p2m_open "ModularCurve.PDPairing ModularCurve"

open CongruenceSubgroup ModularCurve.Period
open scoped MatrixGroups

private noncomputable def tAux {G : Type*} [Group G] (H : Subgroup G) (g : G) (q : G ⧸ H) : ↥H :=
  ⟨(g • q).out⁻¹ * (g * q.out), by
    refine QuotientGroup.eq.mp ?_
    rw [QuotientGroup.out_eq']
    show g • q = ((g * q.out : G) : G ⧸ H)
    rw [show ((g * q.out : G) : G ⧸ H) = g • ((q.out : G) : G ⧸ H) from rfl,
      QuotientGroup.out_eq']⟩

private theorem coe_tAux {G : Type*} [Group G] (H : Subgroup G) (g : G) (q : G ⧸ H) :
    ((tAux H g q : ↥H) : G) = (g • q).out⁻¹ * (g * q.out) := rfl

private theorem toAdditiveLeft_transfer_apply {G K : Type*} [Group G] [Group K]
    (H : Subgroup G) [H.FiniteIndex] {A : Type*} [AddCommGroup A]
    (c : ↥H →* K) (φ : Additive K →+ A) (g : G) :
    MonoidHom.toAdditiveLeft
        (MonoidHom.transfer ((AddMonoidHom.toMultiplicativeRight φ).comp c)) (Additive.ofMul g) =
      (letI := H.fintypeQuotientOfFiniteIndex
       ∑ q : G ⧸ H, φ (Additive.ofMul (c (tAux H g q)))) := by
  letI := H.fintypeQuotientOfFiniteIndex
  set ϕ : ↥H →* Multiplicative A := (AddMonoidHom.toMultiplicativeRight φ).comp c with hϕ
  have hval : MonoidHom.toAdditiveLeft (MonoidHom.transfer ϕ) (Additive.ofMul g)
      = Multiplicative.toAdd (MonoidHom.transfer ϕ g) := rfl
  rw [hval, MonoidHom.transfer_def ϕ (default : H.LeftTransversal) g]
  simp only [Subgroup.leftTransversals.diff]
  rw [toAdd_prod]
  refine (Fintype.sum_bijective (g • ·) (MulAction.bijective g) _ _ fun q => ?_).symm
  have hα : ∀ q : G ⧸ H,
      (((default : H.LeftTransversal).2.leftQuotientEquiv q : G)) = q.out := fun q =>
    Subgroup.IsComplement.leftQuotientEquiv_apply Quotient.out_eq' q
  have hβ : (((g • (default : H.LeftTransversal)).2.leftQuotientEquiv (g • q) : G))
      = g * q.out := by
    rw [Subgroup.smul_apply_eq_smul_apply_inv_smul, inv_smul_smul, hα, smul_eq_mul]
  have hcoe : ((tAux H g q : ↥H) : G)
      = ((((default : H.LeftTransversal).2.leftQuotientEquiv (g • q) : G))⁻¹ *
          ((g • (default : H.LeftTransversal)).2.leftQuotientEquiv (g • q) : G)) := by
    rw [coe_tAux, hα, hβ]
  show φ (Additive.ofMul (c (tAux H g q))) = Multiplicative.toAdd (ϕ _)
  simp only [hϕ, MonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_toMultiplicativeRight,
    toAdd_ofAdd]
  congr 3
  exact Subtype.ext hcoe

private theorem sum_tAux_congr {G K : Type*} [Group G] [Group K] {A : Type*} [AddCommGroup A]
    (H₁ H₂ : Subgroup G) (h : H₁ = H₂) [H₁.FiniteIndex] [H₂.FiniteIndex]
    (c₁ : ↥H₁ →* K) (c₂ : ↥H₂ →* K)
    (hc : ∀ (x : G) (h₁ : x ∈ H₁) (h₂ : x ∈ H₂), c₁ ⟨x, h₁⟩ = c₂ ⟨x, h₂⟩)
    (φ : Additive K →+ A) (g : G) :
    (letI := H₁.fintypeQuotientOfFiniteIndex
     ∑ q : G ⧸ H₁, φ (Additive.ofMul (c₁ (tAux H₁ g q)))) =
    (letI := H₂.fintypeQuotientOfFiniteIndex
     ∑ q : G ⧸ H₂, φ (Additive.ofMul (c₂ (tAux H₂ g q)))) := by
  subst h
  have hc' : c₁ = c₂ := MonoidHom.ext fun x => hc x.1 x.2 x.2
  subst hc'
  rfl

private theorem coresAdd_comp_apply {G K : Type*} [Group G] [Group K] (H : Subgroup G) [H.FiniteIndex]
    {A : Type*} [AddCommGroup A] (c : ↥H →* K) (φ : Additive K →+ A) (g : G) :
    coresAdd H (φ.comp (MonoidHom.toAdditive c)) (Additive.ofMul g) =
      (letI := H.fintypeQuotientOfFiniteIndex
       ∑ q : G ⧸ H, φ (Additive.ofMul (c (tAux H g q)))) := by
  have hcomp : AddMonoidHom.toMultiplicativeRight (φ.comp (MonoidHom.toAdditive c))
      = (AddMonoidHom.toMultiplicativeRight φ).comp c := MonoidHom.ext fun _ => rfl
  rw [coresAdd, hcomp]
  exact toAdditiveLeft_transfer_apply H c φ g

section Levels

variable (N q : ℕ) [NeZero N] [NeZero q]

omit [NeZero N] in

private theorem gamma0HUpper_eq_range (hNN : N ∣ N * q) (hqq : q ∣ N * q / N) :
    Gamma0HUpper N q = (iotaDeg0 N (N * q) q hNN hqq).range := by
  ext x
  constructor
  · intro hx
    have hb : (q : ℤ) ∣ (x : SL(2, ℤ)) 0 1 := dvd_of_mem_Gamma0HUpper N q ⟨x, hx⟩
    have hmem : conjUpperMat q (x : SL(2, ℤ)) hb ∈ Gamma0 (N * q) := by
      rw [Gamma0_mem, conjUpperMat_apply_10, Int.cast_mul]
      have hc : ((N : ℕ) : ℤ) ∣ (x : SL(2, ℤ)) 1 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp x.2)
      obtain ⟨t, ht⟩ := hc
      rw [ht]
      push_cast
      rw [show (N : ZMod (N * q)) * (t : ZMod (N * q)) * (q : ZMod (N * q))
          = ((N * q : ℕ) : ZMod (N * q)) * (t : ZMod (N * q)) by push_cast; ring,
        ZMod.natCast_self, zero_mul]
    refine ⟨⟨conjUpperMat q (x : SL(2, ℤ)) hb, hmem⟩, ?_⟩
    apply Subtype.ext
    exact conjLowerMat_conjUpperMat q (x : SL(2, ℤ)) hb
      (dvd_entry0 N (N * q) q hNN hqq ⟨conjUpperMat q (x : SL(2, ℤ)) hb, hmem⟩)
  · rintro ⟨γ, rfl⟩
    rw [Subgroup.mem_subgroupOf, mem_Gamma0Upper, ZMod.intCast_zmod_eq_zero_iff_dvd]
    show (q : ℤ) ∣ (conjLowerMat q (γ : SL(2, ℤ)) (dvd_entry0 N (N * q) q hNN hqq γ)) 0 1
    simp [conjLowerMat]

omit [NeZero N] in

private theorem conjL0_eq_incl_preimage (hNN : N ∣ N * q) (hqq : q ∣ N * q / N) (h11 : 1 ∣ N * q / N)
    (x : ↥(Gamma0 N)) (h₁ : x ∈ Gamma0HUpper N q) (h₂ : x ∈ (iotaDeg0 N (N * q) q hNN hqq).range) :
    conjL0 N q ⟨x, h₁⟩ =
      ((iotaDeg0 N (N * q) 1 hNN h11).comp
        ((iotaDeg0 N (N * q) q hNN hqq).ofInjective (iotaDeg0_injective N (N * q) q hNN hqq)).symm.toMonoidHom)
        ⟨x, h₂⟩ := by

  set γ : ↥(Gamma0 (N * q)) :=
    ((iotaDeg0 N (N * q) q hNN hqq).ofInjective (iotaDeg0_injective N (N * q) q hNN hqq)).symm ⟨x, h₂⟩ with hγ
  have hγx : iotaDeg0 N (N * q) q hNN hqq γ = x := by
    have := MonoidHom.ofInjective_apply (f := iotaDeg0 N (N * q) q hNN hqq)
      (iotaDeg0_injective N (N * q) q hNN hqq) (x := γ)
    rw [hγ] at this ⊢
    have h' := congrArg Subtype.val
      (((iotaDeg0 N (N * q) q hNN hqq).ofInjective (iotaDeg0_injective N (N * q) q hNN hqq)).apply_symm_apply
        ⟨x, h₂⟩)
    rw [MonoidHom.ofInjective_apply] at h'
    exact h'
  show conjL0 N q ⟨x, h₁⟩ = iotaDeg0 N (N * q) 1 hNN h11 γ

  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hb : (q : ℤ) ∣ (x : SL(2, ℤ)) 0 1 := dvd_of_mem_Gamma0HUpper N q ⟨x, h₁⟩
  have hent : ∀ i j, (x : SL(2, ℤ)) i j = (conjLowerMat q (γ : SL(2, ℤ)) (dvd_entry0 N (N * q) q hNN hqq γ)) i j := by
    intro i j
    have := congrArg (fun y : ↥(Gamma0 N) => ((y : SL(2, ℤ)) i j)) hγx
    exact this.symm
  have h00 := hent 0 0; have h01 := hent 0 1; have h10 := hent 1 0; have h11' := hent 1 1
  simp only [conjLowerMat, Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h00 h01 h10 h11'
  show (conjUpperMat q (x : SL(2, ℤ)) (dvd_of_mem_Gamma0HUpper N q ⟨x, h₁⟩)) i j =
    (conjLowerMat 1 (γ : SL(2, ℤ)) (dvd_entry0 N (N * q) 1 hNN h11 γ)) i j
  fin_cases i <;> fin_cases j <;>
    simp only [conjUpperMat, conjLowerMat, Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.zero_eta,
      Fin.isValue, Fin.mk_one, Nat.cast_one, mul_one, Int.ediv_one]
  · exact h00
  · rw [h01, Int.mul_ediv_cancel _ hq0]
  · rw [h10, Int.ediv_mul_cancel (dvd_entry0 N (N * q) q hNN hqq γ)]
  · exact h11'

omit [NeZero N] in

private theorem heckeT0_eq_jDeg0_iDeg0 (A : Type*) [AddCommGroup A]
    (hNN : N ∣ N * q) (hqq : q ∣ N * q / N) (h11 : 1 ∣ N * q / N) [NeZero (N * q)]
    (φ : Additive ↥(Gamma0 N) →+ A) :
    heckeT0 N q A φ = jDeg0 N (N * q) q ℤ A hNN hqq (iDeg0 N (N * q) 1 ℤ A hNN h11 φ) := by
  refine AddMonoidHom.ext fun a => ?_
  obtain ⟨g, rfl⟩ : ∃ g : ↥(Gamma0 N), Additive.ofMul g = a := ⟨Additive.toMul a, rfl⟩
  rw [heckeT0_apply, toAdditiveLeft_transfer_apply]
  show _ = coresAdd _ (pushChar0 N (N * q) q A hNN hqq (iDeg0 N (N * q) 1 ℤ A hNN h11 φ)) (Additive.ofMul g)
  have hpush : pushChar0 N (N * q) q A hNN hqq (iDeg0 N (N * q) 1 ℤ A hNN h11 φ)
      = φ.comp (MonoidHom.toAdditive ((iotaDeg0 N (N * q) 1 hNN h11).comp
          ((iotaDeg0 N (N * q) q hNN hqq).ofInjective
            (iotaDeg0_injective N (N * q) q hNN hqq)).symm.toMonoidHom)) := by
    ext; rfl
  rw [hpush, coresAdd_comp_apply]
  exact sum_tAux_congr _ _ (gamma0HUpper_eq_range N q hNN hqq) (conjL0 N q) _
    (conjL0_eq_incl_preimage N q hNN hqq h11) φ g

omit [NeZero N] in

private theorem isParabolicHom_iDeg0 (N' d : ℕ) [NeZero d] (hNN' : N ∣ N') (hdd : d ∣ N' / N)
    (A : Type*) [AddCommGroup A] (ψ : Additive ↥(Gamma0 N) →+ A) (hψ : IsParabolicHom (Gamma0 N) ψ) :
    IsParabolicHom (Gamma0 N') (iDeg0 N N' d ℤ A hNN' hdd ψ) := by
  intro γ hγ
  show ψ (Additive.ofMul (iotaDeg0 N N' d hNN' hdd γ)) = 0
  apply hψ
  have htr : (((iotaDeg0 N N' d hNN' hdd γ : ↥(Gamma0 N)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace
      = (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).trace := by
    rw [Matrix.trace_fin_two, Matrix.trace_fin_two]
    show (conjLowerMat d (γ : SL(2, ℤ)) (dvd_entry0 N N' d hNN' hdd γ)) 0 0 +
        (conjLowerMat d (γ : SL(2, ℤ)) (dvd_entry0 N N' d hNN' hdd γ)) 1 1 = _
    simp [conjLowerMat]
  rw [htr]
  exact hγ

private theorem pairZFun_heckeT0_transpose [IsFreeGroup ↥(Gamma 4)] [NeZero (N * q)]
    (hNN : N ∣ N * q) (hqq : q ∣ N * q / N) (h11 : 1 ∣ N * q / N)
    (φ ψ : Additive ↥(Gamma0 N) →+ ℤ) (hφ : IsParabolicHom (Gamma0 N) φ) (hψ : IsParabolicHom (Gamma0 N) ψ) :
    pairZFun N (heckeT0 N q ℤ φ) ψ =
      pairZFun N φ (jDeg0 N (N * q) 1 ℤ ℤ hNN h11 (iDeg0 N (N * q) q ℤ ℤ hNN hqq ψ)) := by
  rw [heckeT0_eq_jDeg0_iDeg0 N q ℤ hNN hqq h11,
    ModularCurve.PDPairing.pairZFun_jDeg0_iDeg0 N (N * q) q hNN hqq _ ψ
      (isParabolicHom_iDeg0 N (N * q) 1 hNN h11 ℤ φ hφ) hψ,
    pairZFun_swap (N * q), ← ModularCurve.PDPairing.pairZFun_jDeg0_iDeg0 N (N * q) 1 hNN h11 _ φ
      (isParabolicHom_iDeg0 N (N * q) q hNN hqq ℤ ψ hψ) hφ,
    ← pairZFun_swap N]

end Levels
p2m_reactivate "P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.TransferNaturality P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier.ParabolicDuality"

end ModularCurve.PDPairing.HeckeTranspose
p2m_reactivate "P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.TransferNaturality P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier.ParabolicDuality"
p2m_reactivate "P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.TransferNaturality P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier.ParabolicDuality"
p2m_reactivate "P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.TransferNaturality P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier.ParabolicDuality"

namespace CohCarrier
p2m_export "CohCarrier" "heckeTL gamma0Units_surjective diamondL diamondL_eq_diamondRaw coresAdd mem_Gamma0Upper GammaH mem_GammaH_iff GammaH_le_Gamma0 GammaH_top H1 conjUpperMat conjUpperMat_apply_10 conjL heckeT conjHom conjLowerMat LevelLE iotaDeg iDeg' iDegL conjLowerMat_conjUpperMat iotaDeg_injective pushChar jDeg jDegL isParabolicHom_heckeT_top jDegL_mem_parabolicHoms"
namespace ParabolicDuality
p2m_open "CohCarrier"

p2m_open "CongruenceSubgroup ModularCurve.Period ModularCurve.PDPairing P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.ModularCurve.PDPairing P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.TransferNaturality"
open scoped MatrixGroups

private scoped instance freeGammaFour : IsFreeGroup ↥(Gamma 4) := ModularCurve.PDPairing.isFreeGroup_Gamma_four

section Bridges

variable (M M' : ℕ) (d : ℕ)

private theorem ofTop_iDegL {A : Type*} [AddCommGroup A] [NeZero d] (h : LevelLE M M' ⊤ ⊤ d) (φ : H1 M ⊤ A) :
    ofTop M' A (iDegL M M' ⊤ ⊤ d A ℤ h φ) = iDeg0 M M' d ℤ A h.dvd h.ddvd (ofTop M A φ) := by
  ext γ
  show φ (Additive.ofMul (iotaDeg M M' ⊤ ⊤ d h ((topIso M').symm γ))) =
    φ (Additive.ofMul ((topIso M).symm (iotaDeg0 M M' d h.dvd h.ddvd γ)))
  congr 2

private theorem topIso_iotaDeg [NeZero d] (h : LevelLE M M' ⊤ ⊤ d) (γ : ↥(GammaH M' ⊤)) :
    topIso M (iotaDeg M M' ⊤ ⊤ d h γ) = iotaDeg0 M M' d h.dvd h.ddvd (topIso M' γ) :=
  Subtype.ext rfl

private theorem ofTop_jDegL {A : Type*} [AddCommGroup A] [NeZero M'] [NeZero d] (h : LevelLE M M' ⊤ ⊤ d)
    (φ : H1 M' ⊤ A) :
    ofTop M A (jDegL M M' ⊤ ⊤ d A ℤ h φ) = jDeg0 M M' d ℤ A h.dvd h.ddvd (ofTop M' A φ) := by
  refine AddMonoidHom.ext fun a => ?_
  obtain ⟨γ, rfl⟩ : ∃ γ : ↥(Gamma0 M), Additive.ofMul γ = a := ⟨Additive.toMul a, rfl⟩
  rw [ofTop_apply]
  have hφ : φ = (ofTop M' A φ).comp (MonoidHom.toAdditive (topIso M').toMonoidHom) := by
    ext δ
    show φ δ = φ (Additive.ofMul ((topIso M').symm (topIso M' (Additive.toMul δ))))
    rw [MulEquiv.symm_apply_apply]
    rfl
  have key := cores_push_natural (topIso M) (topIso M') (iotaDeg M M' ⊤ ⊤ d h) (iotaDeg0 M M' d h.dvd h.ddvd)
    (iotaDeg_injective M M' ⊤ ⊤ d h) (iotaDeg0_injective M M' d h.dvd h.ddvd) (topIso_iotaDeg M M' d h)
    (ofTop M' A φ) ((topIso M).symm γ)
  rw [MulEquiv.apply_symm_apply] at key
  conv_lhs => rw [hφ]
  exact key

variable (ℓ : ℕ)

private theorem ofTop_heckeT {A : Type*} [AddCommGroup A] [NeZero ℓ] (φ : H1 M ⊤ A) :
    ofTop M A (heckeT M ⊤ ℓ A φ) = heckeT0 M ℓ A (ofTop M A φ) := by
  refine AddMonoidHom.ext fun a => ?_
  obtain ⟨γ, rfl⟩ : ∃ γ : ↥(Gamma0 M), Additive.ofMul γ = a := ⟨Additive.toMul a, rfl⟩
  rw [ofTop_apply, ← heckeT0_apply_eq_heckeT_top_apply M ℓ A φ (ofTop M A φ) (ofTop_agree M A φ)]
  rfl

end Bridges
p2m_reactivate "P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.TransferNaturality P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier.ParabolicDuality"

section Levels

variable (M : ℕ)

private abbrev Lz0 : Type := ↥(parabolicHoms ℤ (Gamma0 M) ℤ)

private abbrev Lz : Type := ↥(parabolicHoms ℤ (GammaH M ⊤) ℤ)

private def latIso : Lz M ≃ₗ[ℤ] Lz0 M where
  toFun x := ⟨ofTop M ℤ x, isParabolicHom_ofTop M ℤ x.2⟩
  invFun y := ⟨toTop M ℤ y, isParabolicHom_toTop M ℤ y.2⟩
  map_add' x y := Subtype.ext (map_add (ofTop M ℤ) x.1 y.1)
  map_smul' r x := Subtype.ext (map_zsmul (ofTop M ℤ) r x.1)
  left_inv x := Subtype.ext (toTop_ofTop M ℤ x.1)
  right_inv y := Subtype.ext (ofTop_toTop M ℤ y.1)

private theorem coe_latIso (x : Lz M) : ((latIso M x : Lz0 M) : Additive ↥(Gamma0 M) →+ ℤ) = ofTop M ℤ x := rfl

private def wz : Lz M →ₗ[ℤ] Lz M :=
  (wCharL M ℤ ℤ).restrict fun φ hφ => wChar_mem_parabolicHoms M ℤ ℤ φ hφ

private theorem coe_wz (x : Lz M) : ((wz M x : Lz M) : H1 M ⊤ ℤ) = wChar M ℤ x := rfl

private theorem wz_wz [NeZero M] (x : Lz M) : wz M (wz M x) = x := Subtype.ext (wChar_wChar M ℤ x.1)

private def wzEquiv [NeZero M] : Lz M ≃ₗ[ℤ] Lz M :=
  { wz M with invFun := wz M, left_inv := wz_wz M, right_inv := wz_wz M }

private theorem exists_forms : ∃ c : ℤ, c ≠ 0 ∧ ∀ (N : ℕ) [NeZero N],
    ∃ B : Lz0 N →ₗ[ℤ] Lz0 N →ₗ[ℤ] ℤ, c • B = pairZ N ∧
      (∀ x, (∀ y, (3 : ℤ) ∣ B x y) → ∃ x', x = (3 : ℤ) • x') ∧
      (∀ y, (∀ x, (3 : ℤ) ∣ B x y) → ∃ y', y = (3 : ℤ) • y') :=
  exists_forall_smul_eq_pairZ_and_perfect_mod_three

private noncomputable def cU : ℤ := exists_forms.choose

private theorem cU_ne_zero : cU ≠ 0 := exists_forms.choose_spec.1

private noncomputable def BU [NeZero M] : Lz0 M →ₗ[ℤ] Lz0 M →ₗ[ℤ] ℤ := (exists_forms.choose_spec.2 M).choose

private theorem cU_smul_BU [NeZero M] : cU • BU M = pairZ M := (exists_forms.choose_spec.2 M).choose_spec.1

private theorem BU_mod_three_right [NeZero M] :
    ∀ y : Lz0 M, (∀ x, (3 : ℤ) ∣ BU M x y) → ∃ y', y = (3 : ℤ) • y' :=
  (exists_forms.choose_spec.2 M).choose_spec.2.2

private theorem cU_mul_BU [NeZero M] (x y : Lz0 M) :
    cU * BU M x y = pairZFun M (x : Additive ↥(Gamma0 M) →+ ℤ) (y : Additive ↥(Gamma0 M) →+ ℤ) := by
  have h := LinearMap.congr_fun₂ (cU_smul_BU M) x y
  rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul] at h
  exact h

private noncomputable def Bw [NeZero M] : Lz M →ₗ[ℤ] Lz M →ₗ[ℤ] ℤ :=
  (BU M).compl₁₂ (latIso M).toLinearMap ((latIso M).toLinearMap ∘ₗ wz M)

private theorem Bw_apply [NeZero M] (x y : Lz M) : Bw M x y = BU M (latIso M x) (latIso M (wz M y)) := rfl

private theorem cU_mul_Bw [NeZero M] (x y : Lz M) :
    cU * Bw M x y = pairZFun M (ofTop M ℤ x) (ofTop M ℤ (wChar M ℤ y)) := by
  rw [Bw_apply, cU_mul_BU]
  rfl

end Levels
p2m_reactivate "P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.TransferNaturality P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier.ParabolicDuality"

section LevelData

variable (M M' d : ℕ)

private theorem levelLE_top (hMM' : M ∣ M') (hd : d ∣ M' / M) : LevelLE M M' ⊤ ⊤ d :=
  ⟨hMM', hd, fun _ _ => Subgroup.mem_top _⟩

variable (ℓ : ℕ)

private theorem dvd_level_mul : M ∣ M * ℓ := dvd_mul_right M ℓ

private theorem level_mul_div [NeZero M] : M * ℓ / M = ℓ :=
  Nat.mul_div_cancel_left ℓ (Nat.pos_of_ne_zero (NeZero.ne M))

private theorem dvd_level_mul_div [NeZero M] : ℓ ∣ M * ℓ / M := by rw [level_mul_div]

private theorem one_dvd_level_mul_div : 1 ∣ M * ℓ / M := one_dvd _

private theorem hℓ1 [NeZero M] : ℓ * 1 = M * ℓ / M := by rw [mul_one, level_mul_div]

private theorem h1ℓ [NeZero M] : 1 * ℓ = M * ℓ / M := by rw [one_mul, level_mul_div]

end LevelData
p2m_reactivate "P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.TransferNaturality P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier.ParabolicDuality"

section Twist

variable (M M' d d' : ℕ) [NeZero M] [NeZero M'] [NeZero d] [NeZero d']

private def wEquiv : ↥(GammaH M ⊤) ≃* ↥(GammaH M ⊤) :=
  MonoidHom.toMulEquiv (wConj M) (wConj M) (MonoidHom.ext (wConj_wConj M)) (MonoidHom.ext (wConj_wConj M))

private theorem jDegL_wCharL (A : Type*) [AddCommGroup A] (R : Type*) [Semiring R] [Module R A]
    (h : LevelLE M M' ⊤ ⊤ d) (h' : LevelLE M M' ⊤ ⊤ d') (hdd' : d * d' = M' / M) (φ : H1 M' ⊤ A) :
    jDegL M M' ⊤ ⊤ d A R h (wCharL M' A R φ) = wCharL M A R (jDegL M M' ⊤ ⊤ d' A R h' φ) := by
  refine AddMonoidHom.ext fun a => ?_
  obtain ⟨g, rfl⟩ : ∃ g : ↥(GammaH M ⊤), Additive.ofMul g = a := ⟨Additive.toMul a, rfl⟩
  exact cores_push_natural (wEquiv M) (wEquiv M') (iotaDeg M M' ⊤ ⊤ d h) (iotaDeg M M' ⊤ ⊤ d' h')
    (iotaDeg_injective M M' ⊤ ⊤ d h) (iotaDeg_injective M M' ⊤ ⊤ d' h') (wConj_iotaDeg M M' d d' h h' hdd') φ g

end Twist
p2m_reactivate "P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.TransferNaturality P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier.ParabolicDuality"

section Hecke

variable (M ℓ : ℕ) [NeZero ℓ]

omit [NeZero ℓ] in

private theorem hLℓ [NeZero M] : LevelLE M (M * ℓ) ⊤ ⊤ ℓ := levelLE_top M (M * ℓ) ℓ (dvd_level_mul M ℓ)
    (dvd_level_mul_div M ℓ)

omit [NeZero ℓ] in
private theorem hL1 [NeZero M] : LevelLE M (M * ℓ) ⊤ ⊤ 1 :=
  levelLE_top M (M * ℓ) 1 (dvd_level_mul M ℓ) (one_dvd_level_mul_div M ℓ)

private scoped instance neZero_level_mul [NeZero M] : NeZero (M * ℓ) := ⟨mul_ne_zero (NeZero.ne M) (NeZero.ne ℓ)⟩

private noncomputable def heckeT' [NeZero M] (A : Type*) [AddCommGroup A] : H1 M ⊤ A →+ H1 M ⊤ A :=
  (jDegL M (M * ℓ) ⊤ ⊤ 1 A ℤ (hL1 M ℓ)).toAddMonoidHom.comp (iDegL M (M * ℓ) ⊤ ⊤ ℓ A ℤ (hLℓ M ℓ)).toAddMonoidHom

private theorem heckeT'_apply [NeZero M] (A : Type*) [AddCommGroup A] (φ : H1 M ⊤ A) :
    heckeT' M ℓ A φ = jDegL M (M * ℓ) ⊤ ⊤ 1 A ℤ (hL1 M ℓ) (iDegL M (M * ℓ) ⊤ ⊤ ℓ A ℤ (hLℓ M ℓ) φ) := rfl

private theorem heckeT_eq [NeZero M] (A : Type*) [AddCommGroup A] (φ : H1 M ⊤ A) :
    heckeT M ⊤ ℓ A φ = jDegL M (M * ℓ) ⊤ ⊤ ℓ A ℤ (hLℓ M ℓ) (iDegL M (M * ℓ) ⊤ ⊤ 1 A ℤ (hL1 M ℓ) φ) := by
  have hinj : Function.Injective (ofTop M A) :=
    Function.LeftInverse.injective (g := toTop M A) (toTop_ofTop M A)
  apply hinj
  rw [ofTop_heckeT, ofTop_jDegL, ofTop_iDegL,
    HeckeTranspose.heckeT0_eq_jDeg0_iDeg0 M ℓ A (dvd_level_mul M ℓ) (dvd_level_mul_div M ℓ)
      (one_dvd_level_mul_div M ℓ)]

private theorem wChar_heckeT' [NeZero M] (A : Type*) [AddCommGroup A] (z : H1 M ⊤ A) :
    wChar M A (heckeT' M ℓ A z) = heckeT M ⊤ ℓ A (wChar M A z) := by
  rw [heckeT'_apply, heckeT_eq]
  show wCharL M A ℤ (jDegL M (M * ℓ) ⊤ ⊤ 1 A ℤ (hL1 M ℓ) (iDegL M (M * ℓ) ⊤ ⊤ ℓ A ℤ (hLℓ M ℓ) z)) =
    jDegL M (M * ℓ) ⊤ ⊤ ℓ A ℤ (hLℓ M ℓ) (iDegL M (M * ℓ) ⊤ ⊤ 1 A ℤ (hL1 M ℓ) (wCharL M A ℤ z))
  rw [← jDegL_wCharL M (M * ℓ) ℓ 1 A ℤ (hLℓ M ℓ) (hL1 M ℓ) (hℓ1 M ℓ),
    iDegL_wCharL M (M * ℓ) 1 ℓ A ℤ (hL1 M ℓ) (hLℓ M ℓ) (h1ℓ M ℓ)]

private theorem heckeT'_wChar [NeZero M] (A : Type*) [AddCommGroup A] (y : H1 M ⊤ A) :
    heckeT' M ℓ A (wChar M A y) = wChar M A (heckeT M ⊤ ℓ A y) := by
  have h := wChar_heckeT' M ℓ A (wChar M A y)
  rw [wChar_wChar] at h
  rw [← h, wChar_wChar]

private theorem pairZFun_ofTop_heckeT [NeZero M] (φ ψ : H1 M ⊤ ℤ) (hφ : IsParabolicHom (GammaH M ⊤) φ)
    (hψ : IsParabolicHom (GammaH M ⊤) ψ) :
    pairZFun M (ofTop M ℤ (heckeT M ⊤ ℓ ℤ φ)) (ofTop M ℤ ψ) =
      pairZFun M (ofTop M ℤ φ) (ofTop M ℤ (heckeT' M ℓ ℤ ψ)) := by
  rw [ofTop_heckeT, heckeT'_apply, ofTop_jDegL, ofTop_iDegL]
  exact HeckeTranspose.pairZFun_heckeT0_transpose M ℓ (dvd_level_mul M ℓ) (dvd_level_mul_div M ℓ)
    (one_dvd_level_mul_div M ℓ) _ _ (isParabolicHom_ofTop M ℤ hφ) (isParabolicHom_ofTop M ℤ hψ)

private noncomputable def Tz : Lz M →ₗ[ℤ] Lz M :=
  (heckeTL M ⊤ ℤ ℓ).restrict fun φ hφ => isParabolicHom_heckeT_top M ℓ ℤ φ hφ

private theorem coe_Tz (x : Lz M) : ((Tz M ℓ x : Lz M) : H1 M ⊤ ℤ) = heckeT M ⊤ ℓ ℤ x := rfl

private theorem Bw_Tz [NeZero M] (x y : Lz M) : Bw M (Tz M ℓ x) y = Bw M x (Tz M ℓ y) := by
  apply mul_left_cancel₀ cU_ne_zero
  rw [cU_mul_Bw, cU_mul_Bw]
  show pairZFun M (ofTop M ℤ (heckeT M ⊤ ℓ ℤ x)) (ofTop M ℤ (wChar M ℤ y)) =
    pairZFun M (ofTop M ℤ x) (ofTop M ℤ (wChar M ℤ (heckeT M ⊤ ℓ ℤ y)))
  rw [pairZFun_ofTop_heckeT M ℓ _ _ x.2 (isParabolicHom_wChar M ℤ y y.2), heckeT'_wChar]

end Hecke
p2m_reactivate "P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.TransferNaturality P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier.ParabolicDuality"

section Degeneracy

variable (M M' d d' : ℕ) [NeZero M] [NeZero M'] [NeZero d] [NeZero d']
variable (h : LevelLE M M' ⊤ ⊤ d) (h' : LevelLE M M' ⊤ ⊤ d') (hdd' : d * d' = M' / M)

omit [NeZero M] [NeZero M'] in

private theorem isParabolicHom_iDegL {A : Type*} [AddCommGroup A] (R : Type*) [Semiring R] [Module R A]
    (φ : H1 M ⊤ A) (hφ : IsParabolicHom (GammaH M ⊤) φ) :
    IsParabolicHom (GammaH M' ⊤) (iDegL M M' ⊤ ⊤ d A R h φ) := by
  intro γ hγ
  show φ (Additive.ofMul (iotaDeg M M' ⊤ ⊤ d h γ)) = 0
  apply hφ
  have htr : (((iotaDeg M M' ⊤ ⊤ d h γ : ↥(GammaH M ⊤)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace
      = ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace := by
    rw [Matrix.trace_fin_two, Matrix.trace_fin_two]
    show (CohCarrier.conjLowerMat d (γ : SL(2, ℤ)) (h.dvd_entry γ)) 0 0 +
        (CohCarrier.conjLowerMat d (γ : SL(2, ℤ)) (h.dvd_entry γ)) 1 1 = _
    simp [CohCarrier.conjLowerMat]
  rw [htr]
  exact hγ

private def iz : Lz M →ₗ[ℤ] Lz M' :=
  (iDegL M M' ⊤ ⊤ d ℤ ℤ h).restrict fun φ hφ => isParabolicHom_iDegL M M' d h ℤ φ hφ

private noncomputable def jz : Lz M' →ₗ[ℤ] Lz M :=
  (jDegL M M' ⊤ ⊤ d' ℤ ℤ h').restrict fun φ hφ => jDegL_mem_parabolicHoms M M' d' ℤ ℤ h' φ hφ

include hdd' in

private theorem Bw_jz_iz (x : Lz M) (y : Lz M') : Bw M (jz M M' d' h' y) x = Bw M' y (iz M M' d h x) := by
  apply mul_left_cancel₀ cU_ne_zero
  rw [cU_mul_Bw, cU_mul_Bw]
  show pairZFun M (ofTop M ℤ (jDegL M M' ⊤ ⊤ d' ℤ ℤ h' y)) (ofTop M ℤ (wChar M ℤ x)) =
    pairZFun M' (ofTop M' ℤ y) (ofTop M' ℤ (wChar M' ℤ (iDegL M M' ⊤ ⊤ d ℤ ℤ h x)))
  rw [ofTop_jDegL, pairZFun_jDeg0_iDeg0 M M' d' h'.dvd h'.ddvd _ _ (isParabolicHom_ofTop M' ℤ y.2)
      (isParabolicHom_ofTop M ℤ (isParabolicHom_wChar M ℤ x x.2)), ← ofTop_iDegL]
  show _ = pairZFun M' (ofTop M' ℤ y) (ofTop M' ℤ (wCharL M' ℤ ℤ (iDegL M M' ⊤ ⊤ d ℤ ℤ h x)))
  rw [← iDegL_wCharL M M' d' d ℤ ℤ h' h (by rw [mul_comm]; exact hdd')]
  rfl

end Degeneracy
p2m_reactivate "P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.TransferNaturality P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier.ParabolicDuality"

end CohCarrier.ParabolicDuality
p2m_reactivate "P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.TransferNaturality P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier.ParabolicDuality"
p2m_reactivate "P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.TransferNaturality P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier.ParabolicDuality"

namespace CohCarrier
p2m_export "CohCarrier" "heckeTL gamma0Units_surjective diamondL diamondL_eq_diamondRaw coresAdd mem_Gamma0Upper GammaH mem_GammaH_iff GammaH_le_Gamma0 GammaH_top H1 conjUpperMat conjUpperMat_apply_10 conjL heckeT conjHom conjLowerMat LevelLE iotaDeg iDeg' iDegL conjLowerMat_conjUpperMat iotaDeg_injective pushChar jDeg jDegL isParabolicHom_heckeT_top jDegL_mem_parabolicHoms"
namespace ParabolicDuality
p2m_open "CohCarrier"

p2m_open "CongruenceSubgroup ModularCurve.Period ModularCurve.PDPairing P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.ModularCurve.PDPairing P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.MatrixTransfer"
open scoped MatrixGroups

section Bases

variable (M : ℕ)

private scoped instance gammaH_top_finiteIndex [NeZero M] : (GammaH M ⊤).FiniteIndex := by
  rw [GammaH_top]
  infer_instance

private theorem exists_bases [NeZero M] : ∃ (n : ℕ) (b : Module.Basis (Fin n) ℤ (Lz M)),
    ∀ (R : Type) [CommRing R] [IsAddTorsionFree R],
      ∃ bR : Module.Basis (Fin n) R ↥(parabolicHoms R (GammaH M ⊤) R),
        ∀ i, (bR i : Additive ↥(GammaH M ⊤) →+ R) = (Int.castAddHom R).comp (b i : Additive ↥(GammaH M ⊤) →+ ℤ) :=
  exists_basis_parabolicHoms_of_isAddTorsionFree (GammaH M ⊤)

private noncomputable def nB [NeZero M] : ℕ := (exists_bases M).choose

private noncomputable def bZ [NeZero M] : Module.Basis (Fin (nB M)) ℤ (Lz M) := (exists_bases M).choose_spec.choose

private theorem bZ_spec [NeZero M] : ∀ (R : Type) [CommRing R] [IsAddTorsionFree R],
    ∃ bR : Module.Basis (Fin (nB M)) R ↥(parabolicHoms R (GammaH M ⊤) R),
      ∀ i, (bR i : Additive ↥(GammaH M ⊤) →+ R) = (Int.castAddHom R).comp (bZ M i : Additive ↥(GammaH M ⊤) →+ ℤ) :=
  (exists_bases M).choose_spec.choose_spec

variable (𝒪 : Type) [CommRing 𝒪]

private abbrev LO : Type := ↥(parabolicHoms 𝒪 (GammaH M ⊤) 𝒪)

private noncomputable def bO [NeZero M] [IsDomain 𝒪] [CharZero 𝒪] : Module.Basis (Fin (nB M)) 𝒪 (LO M 𝒪) := (bZ_spec
    M 𝒪).choose

private theorem coe_bO [NeZero M] [IsDomain 𝒪] [CharZero 𝒪] (i : Fin (nB M)) :
    (bO M 𝒪 i : H1 M ⊤ 𝒪) = (Int.castAddHom 𝒪).comp (bZ M i : H1 M ⊤ ℤ) := (bZ_spec M 𝒪).choose_spec i

private def castL : Lz M →+ LO M 𝒪 where
  toFun x := ⟨mapCoeff (Int.castAddHom 𝒪) x.1, isParabolicHom_mapCoeff (Int.castAddHom 𝒪) x.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x.1 y.1)

private theorem coe_castL (x : Lz M) : ((castL M 𝒪 x : LO M 𝒪) : H1 M ⊤ 𝒪) = mapCoeff (Int.castAddHom 𝒪) x := rfl

private theorem bO_eq [NeZero M] [IsDomain 𝒪] [CharZero 𝒪] (i : Fin (nB M)) : bO M 𝒪 i = castL M 𝒪 (bZ M i) :=
    Subtype.ext (coe_bO M 𝒪 i)

private noncomputable def BO [NeZero M] [IsDomain 𝒪] [CharZero 𝒪] : LO M 𝒪 →ₗ[𝒪] LO M 𝒪 →ₗ[𝒪] 𝒪 := castForm (bZ M)
    (bO M 𝒪) (Bw M)

private theorem BO_heckeT [NeZero M] [IsDomain 𝒪] [CharZero 𝒪] (ℓ : ℕ) [NeZero ℓ] (x y Tx Ty : LO M 𝒪) (hx : (Tx : H1
    M ⊤ 𝒪) = heckeT M ⊤ ℓ 𝒪 x)
    (hy : (Ty : H1 M ⊤ 𝒪) = heckeT M ⊤ ℓ 𝒪 y) : BO M 𝒪 Tx y = BO M 𝒪 x Ty := by
  let TO : LO M 𝒪 →ₗ[𝒪] LO M 𝒪 := (heckeTL M ⊤ 𝒪 ℓ).restrict fun φ hφ => isParabolicHom_heckeT_top M ℓ 𝒪 φ hφ
  have hTx : Tx = TO x := Subtype.ext hx
  have hTy : Ty = TO y := Subtype.ext hy
  rw [hTx, hTy]
  refine castForm_comm (bZ M) (bO M 𝒪) (Bw M) (castL M 𝒪) (bO_eq M 𝒪) (Tz M ℓ) TO (fun z => ?_) (Bw_Tz M ℓ) x y
  apply Subtype.ext
  show heckeT M ⊤ ℓ 𝒪 (mapCoeff (Int.castAddHom 𝒪) z) = mapCoeff (Int.castAddHom 𝒪) (heckeT M ⊤ ℓ ℤ z)
  exact heckeT_mapCoeff M ℓ (Int.castAddHom 𝒪) z

private theorem BO_diamondL [NeZero M] [IsDomain 𝒪] [CharZero 𝒪] (d : (ZMod M)ˣ) (x y Dx Dy : LO M 𝒪) (hx : (Dx : H1
    M ⊤ 𝒪) = diamondL M ⊤ 𝒪 d x)
    (hy : (Dy : H1 M ⊤ 𝒪) = diamondL M ⊤ 𝒪 d y) : BO M 𝒪 Dx y = BO M 𝒪 x Dy := by
  rw [diamondL_top_apply] at hx hy
  rw [Subtype.ext hx, Subtype.ext hy]

end Bases
p2m_reactivate "P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.TransferNaturality P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier.ParabolicDuality"

section TwoLevels

variable (M M' d d' : ℕ) [NeZero M] [NeZero M'] [NeZero d] [NeZero d']
variable (h : LevelLE M M' ⊤ ⊤ d) (h' : LevelLE M M' ⊤ ⊤ d') (hdd' : d * d' = M' / M)
variable (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪]

include hdd' in

private theorem BO_jDegL_iDegL (x : LO M 𝒪) (y : LO M' 𝒪) (ix : LO M' 𝒪) (jy : LO M 𝒪)
    (hix : (ix : H1 M' ⊤ 𝒪) = iDegL M M' ⊤ ⊤ d 𝒪 𝒪 h x) (hjy : (jy : H1 M ⊤ 𝒪) = jDegL M M' ⊤ ⊤ d' 𝒪 𝒪 h' y) :
    BO M 𝒪 jy x = BO M' 𝒪 y ix := by
  let iO : LO M 𝒪 →ₗ[𝒪] LO M' 𝒪 := (iDegL M M' ⊤ ⊤ d 𝒪 𝒪 h).restrict fun φ hφ => isParabolicHom_iDegL M M' d h 𝒪 φ hφ
  let jO : LO M' 𝒪 →ₗ[𝒪] LO M 𝒪 :=
    (jDegL M M' ⊤ ⊤ d' 𝒪 𝒪 h').restrict fun φ hφ => jDegL_mem_parabolicHoms M M' d' 𝒪 𝒪 h' φ hφ
  have hix' : ix = iO x := Subtype.ext hix
  have hjy' : jy = jO y := Subtype.ext hjy
  rw [hix', hjy']
  refine castForm_adjoint (bZ M) (bO M 𝒪) (Bw M) (castL M 𝒪) (bO_eq M 𝒪) (bZ M') (bO M' 𝒪) (Bw M') (castL M' 𝒪)
    (bO_eq M' 𝒪) (iz M M' d h) iO (fun z => Subtype.ext ?_) (jz M M' d' h') jO (fun z => Subtype.ext ?_)
    (Bw_jz_iz M M' d d' h h' hdd') x y
  · exact iDegL_mapCoeff M M' d (Int.castAddHom 𝒪) h z
  · exact jDegL_mapCoeff M M' d' (Int.castAddHom 𝒪) h' z

end TwoLevels
p2m_reactivate "P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.TransferNaturality P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier.ParabolicDuality"

end CohCarrier.ParabolicDuality
p2m_reactivate "P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.TransferNaturality P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier.ParabolicDuality"
p2m_reactivate "P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.TransferNaturality P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier.ParabolicDuality"

namespace CohCarrier
p2m_export "CohCarrier" "heckeTL gamma0Units_surjective diamondL diamondL_eq_diamondRaw coresAdd mem_Gamma0Upper GammaH mem_GammaH_iff GammaH_le_Gamma0 GammaH_top H1 conjUpperMat conjUpperMat_apply_10 conjL heckeT conjHom conjLowerMat LevelLE iotaDeg iDeg' iDegL conjLowerMat_conjUpperMat iotaDeg_injective pushChar jDeg jDegL isParabolicHom_heckeT_top jDegL_mem_parabolicHoms"
namespace ParabolicDuality
p2m_open "CohCarrier"

private theorem isUnit_intCast_of_not_dvd {𝒪 : Type*} [CommRing 𝒪] [IsLocalRing 𝒪] {p : ℕ} (hp : p.Prime)
    (hpu : ¬ IsUnit (p : 𝒪)) {n : ℤ} (hn : ¬ (p : ℤ) ∣ n) : IsUnit (n : 𝒪) := by
  have hg1 : Int.gcd (p : ℤ) n = 1 := by
    have hg : Int.gcd (p : ℤ) n ∣ p := by
      have h := Int.gcd_dvd_left (a := (p : ℤ)) (b := n)
      exact_mod_cast h
    rcases (Nat.dvd_prime hp).mp hg with h | h
    · exact h
    · exfalso
      apply hn
      have h2 := Int.gcd_dvd_right (a := (p : ℤ)) (b := n)
      rwa [h] at h2
  have hbez : (1 : ℤ) = (p : ℤ) * Int.gcdA (p : ℤ) n + n * Int.gcdB (p : ℤ) n := by
    have h := Int.gcd_eq_gcd_ab (p : ℤ) n
    rwa [hg1, Nat.cast_one] at h
  have h := congrArg (Int.cast : ℤ → 𝒪) hbez
  push_cast at h
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one h.symm with h' | h'
  · exact absurd (isUnit_of_mul_isUnit_left h') hpu
  · exact isUnit_of_mul_isUnit_left h'

private theorem apply_basis_sum {ι : Type*} [Fintype ι] {L : Type*} [AddCommGroup L] [Module ℤ L] (bZ : Module.Basis
    ι ℤ L)
    (Bz : L →ₗ[ℤ] L →ₗ[ℤ] ℤ) (c : ι → ℤ) (i : ι) :
    Bz (bZ i) (bZ.equivFun.symm c) = ∑ j, Bz (bZ i) (bZ j) * c j := by
  rw [bZ.equivFun_symm_apply, map_sum]
  simp only [map_smul, smul_eq_mul, mul_comm]

private theorem not_dvd_det_toMatrix₂ {ι : Type*} [Fintype ι] [DecidableEq ι] {L : Type*} [AddCommGroup L] [Module ℤ
    L] (bZ : Module.Basis ι ℤ L)
    (Bz : L →ₗ[ℤ] L →ₗ[ℤ] ℤ) {p : ℕ} (hp : p.Prime)
    (hBz : ∀ y : L, (∀ x : L, (p : ℤ) ∣ Bz x y) → ∃ y' : L, y = (p : ℤ) • y') :
    ¬ (p : ℤ) ∣ (LinearMap.toMatrix₂ bZ bZ Bz).det := by
  intro hdet
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hdet' : ((LinearMap.toMatrix₂ bZ bZ Bz).map (Int.castRingHom (ZMod p))).det = 0 := by
    show ((Int.castRingHom (ZMod p)).mapMatrix (LinearMap.toMatrix₂ bZ bZ Bz)).det = 0
    rw [← RingHom.map_det, eq_intCast]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet'
  set c : ι → ℤ := fun j => ((v j).val : ℤ) with hc
  have hcv : ∀ j, ((c j : ℤ) : ZMod p) = v j := fun j => by
    simp only [hc, Int.cast_natCast, ZMod.natCast_zmod_val]
  set y : L := bZ.equivFun.symm c with hy
  have hbasis : ∀ i, (p : ℤ) ∣ Bz (bZ i) y := by
    intro i
    rw [hy, apply_basis_sum bZ Bz c i, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have h := congrFun hv i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply, eq_intCast,
      LinearMap.toMatrix₂_apply] at h
    push_cast
    simpa only [hcv] using h
  have hall : ∀ x, (p : ℤ) ∣ Bz x y := by
    intro x
    rw [← bZ.sum_repr x, map_sum, LinearMap.sum_apply]
    refine Finset.dvd_sum fun i _ => ?_
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact (hbasis i).mul_left _
  obtain ⟨y', hy'⟩ := hBz y hall
  rw [← Int.cast_smul_eq_zsmul (R := ℤ), Int.cast_id] at hy'
  have hcy : bZ.equivFun y = c := by rw [hy, LinearEquiv.apply_symm_apply]
  apply hv0
  funext j
  have hcj : c j = (p : ℤ) * bZ.equivFun y' j := by
    rw [← hcy, hy', bZ.equivFun.map_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
  rw [← hcv j, hcj]
  simp

private theorem bijective_toLinearMap₂_of_isUnit_det {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]
    {V : Type*} [AddCommGroup V]
    [Module R V] (b : Module.Basis ι R V) (G : Matrix ι ι R) (hG : IsUnit G.det) :
    Function.Bijective (Matrix.toLinearMap₂ b b G) := by
  have hGu : IsUnit G := (Matrix.isUnit_iff_isUnit_det G).mpr hG
  have hval : ∀ (c : ι → R) (j : ι), Matrix.toLinearMap₂ b b G (b.equivFun.symm c) (b j) = (Matrix.vecMul c G) j := by
    intro c j
    rw [b.equivFun_symm_apply, map_sum, LinearMap.sum_apply]
    simp only [map_smul, LinearMap.smul_apply, Matrix.toLinearMap₂_apply_basis, smul_eq_mul, Matrix.vecMul,
      dotProduct]
  constructor
  · intro x₁ x₂ hx
    have h : Matrix.vecMul (b.equivFun x₁) G = Matrix.vecMul (b.equivFun x₂) G := by
      funext j
      rw [← hval, ← hval, b.equivFun.symm_apply_apply, b.equivFun.symm_apply_apply, hx]
    exact b.equivFun.injective (Matrix.vecMul_injective_of_isUnit hGu h)
  · intro f
    obtain ⟨c, hc⟩ := Matrix.vecMul_surjective_iff_isUnit.mpr hGu (fun j => f (b j))
    refine ⟨b.equivFun.symm c, b.ext fun j => ?_⟩
    rw [hval]
    exact congrFun hc j

private theorem bijective_toLinearMap₂_castGram {𝒪 : Type*} [CommRing 𝒪] [IsLocalRing 𝒪] (p : ℕ) (hp : p.Prime)
    (hpu : ¬ IsUnit (p : 𝒪)) {ι : Type*} [Fintype ι] [DecidableEq ι] {L : Type*} [AddCommGroup L] [Module ℤ L]
    (bZ : Module.Basis ι ℤ L) (Bz : L →ₗ[ℤ] L →ₗ[ℤ] ℤ)
    (hBz : ∀ y : L, (∀ x : L, (p : ℤ) ∣ Bz x y) → ∃ y' : L, y = (p : ℤ) • y')
    {LO : Type*} [AddCommGroup LO] [Module 𝒪 LO] (bO : Module.Basis ι 𝒪 LO) :
    Function.Bijective (Matrix.toLinearMap₂ bO bO ((LinearMap.toMatrix₂ bZ bZ Bz).map (Int.castRingHom 𝒪))) := by
  apply bijective_toLinearMap₂_of_isUnit_det
  have hdet : ((LinearMap.toMatrix₂ bZ bZ Bz).map (Int.castRingHom 𝒪)).det
      = (((LinearMap.toMatrix₂ bZ bZ Bz).det : ℤ) : 𝒪) := by
    show ((Int.castRingHom 𝒪).mapMatrix (LinearMap.toMatrix₂ bZ bZ Bz)).det = _
    rw [← RingHom.map_det, eq_intCast]
  rw [hdet]
  exact isUnit_intCast_of_not_dvd hp hpu (not_dvd_det_toMatrix₂ bZ Bz hp hBz)

end CohCarrier.ParabolicDuality
p2m_reactivate "P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.TransferNaturality P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier.ParabolicDuality"
p2m_reactivate "P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.TransferNaturality P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier.ParabolicDuality"

namespace CohCarrier
p2m_export "CohCarrier" "heckeTL gamma0Units_surjective diamondL diamondL_eq_diamondRaw coresAdd mem_Gamma0Upper GammaH mem_GammaH_iff GammaH_le_Gamma0 GammaH_top H1 conjUpperMat conjUpperMat_apply_10 conjL heckeT conjHom conjLowerMat LevelLE iotaDeg iDeg' iDegL conjLowerMat_conjUpperMat iotaDeg_injective pushChar jDeg jDegL isParabolicHom_heckeT_top jDegL_mem_parabolicHoms"
namespace ParabolicDuality
p2m_open "CohCarrier"

p2m_open "CongruenceSubgroup ModularCurve.Period ModularCurve.PDPairing P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.ModularCurve.PDPairing P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.MatrixTransfer"

section Perfect

private theorem prime_eq_three_or_five_le (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : p = 3 ∨ 5 ≤ p := by
  have h2 := hp.two_le
  have h4 : p ≠ 4 := by
    rintro rfl
    exact absurd hp (by decide)
  omega

variable (M : ℕ) [NeZero M]

private theorem pairZ_eq_cU_mul_BU (x y : Lz0 M) : pairZ M x y = cU * BU M x y := by
  rw [← cU_smul_BU]
  rfl

private theorem BU_nondeg_right (p : ℕ) (hp : p.Prime) (h35 : p = 3 ∨ 5 ≤ p) (y : Lz0 M)
    (hy : ∀ x, (p : ℤ) ∣ BU M x y) : ∃ y', y = (p : ℤ) • y' := by
  rcases h35 with rfl | h5
  · exact BU_mod_three_right M y (by simpa using hy)
  · exact (pairZ_nondegenerate_mod M p hp h5).2 y fun x => by
      rw [pairZ_eq_cU_mul_BU]
      exact Dvd.dvd.mul_left (hy x) cU

private theorem Bw_nondeg_right (p : ℕ) (hp : p.Prime) (h35 : p = 3 ∨ 5 ≤ p) (y : Lz M)
    (hy : ∀ x, (p : ℤ) ∣ Bw M x y) : ∃ y', y = (p : ℤ) • y' := by
  obtain ⟨y₀, hy₀⟩ := BU_nondeg_right M p hp h35 (latIso M (wz M y)) fun x₀ => by
    have h := hy ((latIso M).symm x₀)
    rwa [Bw_apply, LinearEquiv.apply_symm_apply] at h
  refine ⟨wz M ((latIso M).symm y₀), ?_⟩
  rw [← map_zsmul, ← map_zsmul, ← hy₀, LinearEquiv.symm_apply_apply, wz_wz]

variable (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] [IsLocalRing 𝒪]

private theorem bijective_BO (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hpu : ¬ IsUnit (p : 𝒪)) :
    Function.Bijective (BO M 𝒪) := by
  classical
  exact bijective_toLinearMap₂_castGram p hp hpu (bZ M) (Bw M)
    (Bw_nondeg_right M p hp (prime_eq_three_or_five_le p hp hp2)) (bO M 𝒪)

end Perfect
p2m_reactivate "P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.TransferNaturality P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier.ParabolicDuality"

section Family

variable (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪]

private noncomputable def Bfam (M : ℕ) : LO M 𝒪 →ₗ[𝒪] LO M 𝒪 →ₗ[𝒪] 𝒪 :=
  if hM : M = 0 then 0 else (haveI : NeZero M := ⟨hM⟩; BO M 𝒪)

private theorem Bfam_eq (M : ℕ) [NeZero M] : Bfam 𝒪 M = BO M 𝒪 := dif_neg (NeZero.ne M)

end Family
p2m_reactivate "P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.TransferNaturality P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier.ParabolicDuality"

end CohCarrier.ParabolicDuality
p2m_reactivate "P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.TransferNaturality P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier.ParabolicDuality"
p2m_reactivate "P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.TransferNaturality P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms.CohCarrier.ParabolicDuality"

open CohCarrier.ParabolicDuality in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] [IsLocalRing 𝒪]
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hpu : ¬ IsUnit (p : 𝒪)) :
    ∃ B : (M : ℕ) → ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M ⊤) 𝒪) →ₗ[𝒪]
        ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M ⊤) 𝒪) →ₗ[𝒪] 𝒪,
      (∀ (M : ℕ) [NeZero M],
        Function.Bijective (B M) ∧
        (∀ (ℓ : ℕ) [NeZero ℓ] (x y Tx Ty : ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M ⊤) 𝒪)),
            (Tx : CohCarrier.H1 M ⊤ 𝒪) = CohCarrier.heckeT M ⊤ ℓ 𝒪 x →
            (Ty : CohCarrier.H1 M ⊤ 𝒪) = CohCarrier.heckeT M ⊤ ℓ 𝒪 y → B M Tx y = B M x Ty) ∧
        (∀ (d : (ZMod M)ˣ) (x y Dx Dy : ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M ⊤) 𝒪)),
            (Dx : CohCarrier.H1 M ⊤ 𝒪) = CohCarrier.diamondL M ⊤ 𝒪 d x →
            (Dy : CohCarrier.H1 M ⊤ 𝒪) = CohCarrier.diamondL M ⊤ 𝒪 d y → B M Dx y = B M x Dy)) ∧
      (∀ (M M' : ℕ) [NeZero M'] (d d' : ℕ) [NeZero d] [NeZero d']
          (h : CohCarrier.LevelLE M M' ⊤ ⊤ d) (h' : CohCarrier.LevelLE M M' ⊤ ⊤ d') (hdd' : d * d' = M' / M)
          (x : ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M ⊤) 𝒪))
          (y : ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M' ⊤) 𝒪))
          (ix : ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M' ⊤) 𝒪))
          (jy : ↥(ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M ⊤) 𝒪)),
          (ix : CohCarrier.H1 M' ⊤ 𝒪) = CohCarrier.iDegL M M' ⊤ ⊤ d 𝒪 𝒪 h x →
          (jy : CohCarrier.H1 M ⊤ 𝒪) = CohCarrier.jDegL M M' ⊤ ⊤ d' 𝒪 𝒪 h' y →
          B M jy x = B M' y ix) := by
  refine ⟨Bfam 𝒪, fun M _ => ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [Bfam_eq]
    exact bijective_BO M 𝒪 p hp hp2 hpu
  · intro ℓ _ x y Tx Ty hx hy
    rw [Bfam_eq]
    exact BO_heckeT M 𝒪 ℓ x y Tx Ty hx hy
  · intro d x y Dx Dy hx hy
    rw [Bfam_eq]
    exact BO_diamondL M 𝒪 d x y Dx Dy hx hy
  · intro M M' _ d d' _ _ h h' hdd' x y ix jy hix hjy
    haveI : NeZero M := ⟨fun hM => NeZero.ne M' (zero_dvd_iff.mp (hM ▸ h.dvd))⟩
    rw [Bfam_eq, Bfam_eq]
    exact BO_jDegL_iDegL M M' d d' h h' hdd' 𝒪 x y ix jy hix hjy

end S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms
end P2MW
export P2MW.S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms (solution)
