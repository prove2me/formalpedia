-- Prove2me | solution 1 for Deformation.DieudonneModule.exists_surjective_ker_map_of_bottomLayer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/6ffdf562-1d7b-5a08-ab00-8d35e30f1b82

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Theorems.Thm_HopfAlgebra_toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique
import Theorems.Thm_Subalgebra_exists_algHom_comp_val_eq_of_isAlgClosed_of_moduleFinite
import Theorems.Thm_HopfAlgebra_exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Theorems.Thm_HopfAlgebra_eq_of_forall_algHom_algebraicClosure_apply_eq_of_flat_ratLocalizedAt
import Theorems.Thm_GaloisRep_ratLocalizedAt_maximalIdeal_eq_span_natCast
import Theorems.Thm_GaloisRep_exists_bialgHom_surjective_finiteFlat_model_addSubgroup_of_stable
import Theorems.Thm_HopfAlgebra_existsUnique_bialgHom_ratLocalizedAt_forall_apply_comp_eq_and_bijective_of_addEquiv_of_ne_two
import Theorems.Thm_HopfAlgebra_isLocalRing_hopfKer_and_isLocalRing_cartierDual_hopfKer_of_surjective
import Theorems.Thm_GaloisRep_ratLocalizedAt_isLocalRing
import Theorems.Thm_Deformation_DieudonneModule_map_surjective_of_surjective
import Theorems.Thm_CartierDual_isLocalRing_baseChange_and_isLocalRing_cartierDual_baseChange
import Theorems.Thm_CartierDual_isLocalRing_cartierDual_of_bialgHom_surjective
import Theorems.Thm_Deformation_DieudonneModule_exists_finrank_eq_pow_and_natCard_eq_pow_of_isLocalRing_cartierDual
import Theorems.Thm_Deformation_DieudonneModule_exact_map_hopfKerVal_map
import Theorems.Thm_Deformation_DieudonneModule_map_baseChange_surjective_injective_fontaineHodge_of_range_eq_hopfKer
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_DieudonneModule_exists_surjective_ker_map_of_bottomLayer
p2m_attr_erase "instance" "CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange instIsScalarTowerTensorProduct_definitions HopfAlgebra.IsHopfTower.refl"
p2m_attr_erase "simp" "HopfOrder.doubleCmp_tmul HopfOrder.tensorSqHom_tmul HopfOrder.baseChangeHom_tmul HopfAlgebra.FVectStructure.addChar_apply HopfAlgebra.FVectStructure.mk.sizeOf_spec HopfAlgebra.FVectStructure.mk.injEq HopfAlgebra.FVectStructure.unitsAct_apply HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul mem_flatClosure_iff CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

namespace HLG

open scoped TensorProduct

universe u v w

variable {R : Type u} [CommRing R] {k : Type u} [CommRing k] [Algebra R k]
variable {H : Type v} [CommRing H] [HopfAlgebra R H] {HV : Type w} [CommRing HV] [HopfAlgebra R HV]

noncomputable def Φ (c : k) : H ⊗[R] HV →ₗ[R] (k ⊗[R] H) ⊗[k] (k ⊗[R] HV) :=
  TensorProduct.lift
    { toFun := fun u =>
        { toFun := fun v => ((1 : k) ⊗ₜ[R] u) ⊗ₜ[k] (c ⊗ₜ[R] v)
          map_add' := fun v v' => by rw [TensorProduct.tmul_add, TensorProduct.tmul_add]
          map_smul' := fun r v => by
            rw [RingHom.id_apply, ← TensorProduct.tmul_smul, ← TensorProduct.tmul_smul] }
      map_add' := fun u u' => by
        apply LinearMap.ext; intro v
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, TensorProduct.tmul_add, TensorProduct.add_tmul]
      map_smul' := fun r u => by
        apply LinearMap.ext; intro v
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, RingHom.id_apply]
        rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul', TensorProduct.smul_tmul'] }

theorem Φ_tmul (c : k) (u : H) (v : HV) : Φ c (u ⊗ₜ[R] v) = ((1 : k) ⊗ₜ[R] u) ⊗ₜ[k] (c ⊗ₜ[R] v) := rfl

theorem coaction_baseChange_tmul (π : H →ₐc[R] HV) (c : k) (h : H) :
    HopfAlgebra.coaction (Bialgebra.TensorProduct.map (BialgHom.id k k) π : k ⊗[R] H →ₐc[k] k ⊗[R] HV)
        (c ⊗ₜ[R] h) =
      Φ c (HopfAlgebra.coaction π h) := by
  rw [HopfAlgebra.coaction_apply, HopfAlgebra.coaction_apply, TensorProduct.comul_tmul,
    CommSemiring.comul_apply]

  let ℛ := Coalgebra.Repr.arbitrary R h
  conv_lhs => rw [← ℛ.eq]
  conv_rhs => rw [← ℛ.eq]
  simp only [TensorProduct.tmul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.map_tmul, Φ_tmul, AlgHom.id_apply]
  rfl

theorem tmul_mem_hopfKer_baseChange (π : H →ₐc[R] HV) (c : k) {h : H} (hh : h ∈ HopfAlgebra.hopfKer π) :
    c ⊗ₜ[R] h ∈ HopfAlgebra.hopfKer
      (Bialgebra.TensorProduct.map (BialgHom.id k k) π : k ⊗[R] H →ₐc[k] k ⊗[R] HV) := by
  rw [HopfAlgebra.mem_hopfKer_iff, coaction_baseChange_tmul, HopfAlgebra.coaction_eq_of_mem π hh, Φ_tmul]

  have h1 : (c ⊗ₜ[R] (1 : HV)) = c • ((1 : k) ⊗ₜ[R] (1 : HV)) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have h2 : (c ⊗ₜ[R] h) = c • ((1 : k) ⊗ₜ[R] h) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, TensorProduct.tmul_smul, TensorProduct.smul_tmul', ← h2]
  rfl

end HLG

namespace HLBody

open scoped TensorProduct

@[reducible] noncomputable def quotAction {κ N : Type} [Field κ] [AddCommGroup N] [Module κ N]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (N →ₗ[κ] N))
    (V : Submodule κ N) (hV : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ∀ x ∈ V, ρ σ x ∈ V) :
    DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (N ⧸ V) where
  smul σ x := Submodule.mapQ V V (ρ σ) (fun y hy => hV σ y hy) x
  one_smul := fun x => by
    induction x using Submodule.Quotient.induction_on with
    | _ y =>
      show Submodule.mapQ V V (ρ 1) (fun y hy => hV 1 y hy) (Submodule.Quotient.mk y) = Submodule.Quotient.mk y
      rw [Submodule.mapQ_apply, map_one]; rfl
  mul_smul := fun σ τ x => by
    induction x using Submodule.Quotient.induction_on with
    | _ y =>
      show Submodule.mapQ V V (ρ (σ * τ)) (fun y hy => hV (σ * τ) y hy) (Submodule.Quotient.mk y) =
        Submodule.mapQ V V (ρ σ) (fun y hy => hV σ y hy)
          (Submodule.mapQ V V (ρ τ) (fun y hy => hV τ y hy) (Submodule.Quotient.mk y))
      rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.mapQ_apply, map_mul]; rfl
  smul_zero := fun σ => map_zero (Submodule.mapQ V V (ρ σ) (fun y hy => hV σ y hy))
  smul_add := fun σ x y => map_add (Submodule.mapQ V V (ρ σ) (fun y hy => hV σ y hy)) x y

theorem quotAction_smul_def {κ N : Type} [Field κ] [AddCommGroup N] [Module κ N]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (N →ₗ[κ] N))
    (V : Submodule κ N) (hV : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ∀ x ∈ V, ρ σ x ∈ V)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : N ⧸ V) :
    (letI := quotAction ρ V hV; σ • x) = Submodule.mapQ V V (ρ σ) (fun y hy => hV σ y hy) x := rfl

set_option maxHeartbeats 3200000 in

theorem points_hopfKer
    (p : ℕ) [Fact p.Prime]
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Free (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    (HV : Type) [CommRing HV] [HopfAlgebra (GaloisRep.ratLocalizedAt p) HV]
    [Module.Finite (GaloisRep.ratLocalizedAt p) HV] [Module.Free (GaloisRep.ratLocalizedAt p) HV]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) HV]
    (π : H →ₐc[GaloisRep.ratLocalizedAt p] HV) (hπ : Function.Surjective π)
    [Module.Finite (GaloisRep.ratLocalizedAt p) ↥(HopfAlgebra.hopfKer π)]
    [Module.Free (GaloisRep.ratLocalizedAt p) ↥(HopfAlgebra.hopfKer π)]
    {κ : Type} [Field κ] {N : Type} [AddCommGroup N] [Module κ N]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (N →ₗ[κ] N))
    (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ N)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_gal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ h : H, g h = σ (f h)) → e g = ρ σ (e f))
    (V : Submodule κ N)
    (hV : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ∀ x ∈ V, ρ σ x ∈ V)
    (eV : WithConv (HV →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ ↥V)
    (heV : ∀ f : WithConv (HV →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
      ((eV f : ↥V) : N) =
        e (WithConv.toConv ((WithConv.ofConv f).comp (π : H →ₐ[GaloisRep.ratLocalizedAt p] HV)))) :
    ∃ eQ : WithConv (↥(HopfAlgebra.hopfKer π) →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ N ⧸ V,
      (∀ f g, eQ (f * g) = eQ f + eQ g) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (f g : WithConv (↥(HopfAlgebra.hopfKer π) →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
        (∀ h, g h = σ (f h)) → eQ g = Submodule.mapQ V V (ρ σ) (fun y hy => hV σ y hy) (eQ f)) ∧
      (∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        eQ (WithConv.toConv ((WithConv.ofConv f).comp (HopfAlgebra.hopfKer π).val)) =
          Submodule.Quotient.mk (e f)) ∧
      (∀ χ : ↥(HopfAlgebra.hopfKer π) →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ,
        ∃ f : H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ, f.comp (HopfAlgebra.hopfKer π).val = χ) := by
  classical
  haveI : Module.Flat (GaloisRep.ratLocalizedAt p) H := Module.Flat.of_free
  haveI : Module.Flat (GaloisRep.ratLocalizedAt p) ↥(HopfAlgebra.hopfKer π) := Module.Flat.of_free

  let res : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) →
      WithConv (↥(HopfAlgebra.hopfKer π) →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) :=
    fun ν => WithConv.toConv ((WithConv.ofConv ν).comp (HopfAlgebra.hopfKer π).val)
  have hres_def : ∀ ν, res ν = WithConv.toConv ((WithConv.ofConv ν).comp (HopfAlgebra.hopfKer π).val) :=
    fun ν => rfl
  obtain ⟨h9one, h9mul, h9iff⟩ :=
    HopfAlgebra.toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique π hπ (AlgebraicClosure ℚ)

  have hres : ∀ χ : ↥(HopfAlgebra.hopfKer π) →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ,
      ∃ f : H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ, f.comp (HopfAlgebra.hopfKer π).val = χ :=
    fun χ => Subalgebra.exists_algHom_comp_val_eq_of_isAlgClosed_of_moduleFinite
      (HopfAlgebra.hopfKer π) (AlgebraicClosure ℚ) χ

  have hkey : ∀ ν ν' : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ), res ν = res ν' →
      (Submodule.Quotient.mk (e ν) : N ⧸ V) = Submodule.Quotient.mk (e ν') := by
    intro ν ν' h
    have h' : (WithConv.ofConv ν).comp (HopfAlgebra.hopfKer π).val =
        (WithConv.ofConv ν').comp (HopfAlgebra.hopfKer π).val := congrArg WithConv.ofConv h
    obtain ⟨χ, hχ, -⟩ := (h9iff ν ν').mp h'
    rw [eq_comm, Submodule.Quotient.eq, hχ, he_add, add_sub_cancel_left, ← heV (WithConv.toConv χ)]
    exact (eV (WithConv.toConv χ)).2

  have hkey' : ∀ ν ν' : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
      (Submodule.Quotient.mk (e ν) : N ⧸ V) = Submodule.Quotient.mk (e ν') → res ν = res ν' := by
    intro ν ν' h
    rw [eq_comm, Submodule.Quotient.eq] at h
    obtain ⟨χ₀, hχ₀⟩ := eV.surjective ⟨e ν' - e ν, h⟩
    have hval : e ν' - e ν = e (WithConv.toConv ((WithConv.ofConv χ₀).comp (π : H →ₐ[GaloisRep.ratLocalizedAt p] HV))) := by
      rw [← heV χ₀, hχ₀]
    have hν' : ν' = ν * WithConv.toConv ((WithConv.ofConv χ₀).comp (π : H →ₐ[GaloisRep.ratLocalizedAt p] HV)) := by
      apply e.injective
      rw [he_add, ← hval, add_sub_cancel]
    apply congrArg WithConv.toConv
    apply (h9iff ν ν').mpr
    refine ⟨WithConv.ofConv χ₀, hν', fun χ hχ => ?_⟩

    have h1 : e (WithConv.toConv (χ.comp (π : H →ₐ[GaloisRep.ratLocalizedAt p] HV))) =
        e (WithConv.toConv ((WithConv.ofConv χ₀).comp (π : H →ₐ[GaloisRep.ratLocalizedAt p] HV))) := by
      have := congrArg e (hχ.symm.trans hν')
      rw [he_add, he_add] at this
      exact add_left_cancel this
    have h2 := congrArg WithConv.ofConv (e.injective h1)
    simp only [WithConv.ofConv_toConv] at h2
    apply AlgHom.ext
    intro b
    obtain ⟨a, rfl⟩ := hπ b
    exact AlgHom.congr_fun h2 a

  choose lift hlift using hres
  let F : WithConv (↥(HopfAlgebra.hopfKer π) →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) → N ⧸ V :=
    fun χ => Submodule.Quotient.mk (e (WithConv.toConv (lift (WithConv.ofConv χ))))
  have hres_lift : ∀ χ, res (WithConv.toConv (lift (WithConv.ofConv χ))) = χ := by
    intro χ
    rw [hres_def, WithConv.ofConv_toConv, hlift]
  have hF : ∀ ν, F (res ν) = Submodule.Quotient.mk (e ν) := by
    intro ν
    exact hkey _ _ (hres_lift (res ν))
  have hinj : Function.Injective F := by
    intro χ χ' h
    have := hkey' _ _ h
    rwa [hres_lift, hres_lift] at this
  have hsurj : Function.Surjective F := by
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ n =>
      obtain ⟨ν, rfl⟩ := e.surjective n
      exact ⟨res ν, hF ν⟩
  refine ⟨Equiv.ofBijective F ⟨hinj, hsurj⟩, ?_, ?_, ?_, ?_⟩
  ·
    intro f g
    show F (f * g) = F f + F g
    have hf := hres_lift f
    have hg := hres_lift g
    rw [← hf, ← hg, ← h9mul, hF, hF, hF, he_add, Submodule.Quotient.mk_add]
  ·
    intro σ f g hfg
    show F g = Submodule.mapQ V V (ρ σ) (fun y hy => hV σ y hy) (F f)
    let ν := lift (WithConv.ofConv f)
    let ν' : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) :=
      WithConv.toConv (((σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ).restrictScalars
        (GaloisRep.ratLocalizedAt p)).comp ν)
    have hfres : res (WithConv.toConv ν) = f := hres_lift f
    have hg' : res ν' = g := by
      show WithConv.toConv ((WithConv.ofConv ν').comp (HopfAlgebra.hopfKer π).val) = g
      rw [← WithConv.toConv_ofConv g]
      congr 1
      apply AlgHom.ext
      intro h
      show σ (ν (h : H)) = (WithConv.ofConv g) h
      have h1 : (WithConv.ofConv g) h = g h := rfl
      have h2 : f h = ν (h : H) := by
        rw [← hfres]; rfl
      rw [h1, hfg h, h2]
    rw [← hg', hF, ← hfres, hF, Submodule.mapQ_apply]
    congr 1
    exact he_gal σ (WithConv.toConv ν) ν' (fun h => rfl)
  · intro f
    exact hF f
  · intro χ
    exact ⟨lift χ, hlift χ⟩

set_option maxHeartbeats 3200000 in

theorem theta_hopfKer
    (p : ℕ) [Fact p.Prime]
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Free (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    (HV : Type) [CommRing HV] [HopfAlgebra (GaloisRep.ratLocalizedAt p) HV]
    [Module.Finite (GaloisRep.ratLocalizedAt p) HV] [Module.Free (GaloisRep.ratLocalizedAt p) HV]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) HV]
    (π : H →ₐc[GaloisRep.ratLocalizedAt p] HV) (hπ : Function.Surjective π)
    {κ : Type} [Field κ] {N : Type} [AddCommGroup N] [Module κ N]
    (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ N)
    (θ : κ → (H →ₐc[GaloisRep.ratLocalizedAt p] H))
    (hθ : ∀ (a : κ) (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ h : H, g h = f (θ a h)) → e g = a • e f)
    (θV : κ → (HV →ₐc[GaloisRep.ratLocalizedAt p] HV))
    (hθV : ∀ a : κ,
      (θV a : HV →ₐ[GaloisRep.ratLocalizedAt p] HV).comp (π : H →ₐ[GaloisRep.ratLocalizedAt p] HV) =
        (π : H →ₐ[GaloisRep.ratLocalizedAt p] HV).comp (θ a : H →ₐ[GaloisRep.ratLocalizedAt p] H))
    (V : Submodule κ N)
    (eQ : WithConv (↥(HopfAlgebra.hopfKer π) →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ N ⧸ V)
    (heQ_res : ∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
      eQ (WithConv.toConv ((WithConv.ofConv f).comp (HopfAlgebra.hopfKer π).val)) = Submodule.Quotient.mk (e f))
    (hres : ∀ χ : ↥(HopfAlgebra.hopfKer π) →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ,
      ∃ f : H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ, f.comp (HopfAlgebra.hopfKer π).val = χ) :
    ∃ θQ : κ → (↥(HopfAlgebra.hopfKer π) →ₐ[GaloisRep.ratLocalizedAt p] ↥(HopfAlgebra.hopfKer π)),
      (∀ (a : κ) (x : ↥(HopfAlgebra.hopfKer π)), ((θQ a x : ↥(HopfAlgebra.hopfKer π)) : H) = θ a (x : H)) ∧
      (∀ (a : κ) (f g : WithConv (↥(HopfAlgebra.hopfKer π) →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
        (∀ h, g h = f (θQ a h)) → eQ g = a • eQ f) := by
  classical

  have hmem : ∀ (a : κ) (x : ↥(HopfAlgebra.hopfKer π)), (θ a : H →ₐ[GaloisRep.ratLocalizedAt p] H) (x : H) ∈
      HopfAlgebra.hopfKer π := by
    intro a x
    rw [HopfAlgebra.mem_hopfKer_iff, HopfAlgebra.coaction_apply]
    have hx := HopfAlgebra.coaction_eq_of_mem π x.2
    rw [HopfAlgebra.coaction_apply] at hx
    have hcomp : (Algebra.TensorProduct.map (AlgHom.id (GaloisRep.ratLocalizedAt p) H)
          (π : H →ₐ[GaloisRep.ratLocalizedAt p] HV)).comp
        (Algebra.TensorProduct.map (θ a : H →ₐ[GaloisRep.ratLocalizedAt p] H) (θ a : H →ₐ[GaloisRep.ratLocalizedAt p] H)) =
        (Algebra.TensorProduct.map (θ a : H →ₐ[GaloisRep.ratLocalizedAt p] H) (θV a : HV →ₐ[GaloisRep.ratLocalizedAt p] HV)).comp
          (Algebra.TensorProduct.map (AlgHom.id (GaloisRep.ratLocalizedAt p) H) (π : H →ₐ[GaloisRep.ratLocalizedAt p] HV)) := by
      apply Algebra.TensorProduct.ext'
      intro u v
      simp only [AlgHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
      congr 1
      exact (AlgHom.congr_fun (hθV a) v).symm
    have hΔ : Coalgebra.comul (R := GaloisRep.ratLocalizedAt p) ((θ a : H →ₐ[GaloisRep.ratLocalizedAt p] H) (x : H)) =
        Algebra.TensorProduct.map (θ a : H →ₐ[GaloisRep.ratLocalizedAt p] H) (θ a : H →ₐ[GaloisRep.ratLocalizedAt p] H)
          (Coalgebra.comul (R := GaloisRep.ratLocalizedAt p) (x : H)) :=
      (AlgHom.congr_fun (BialgHom.map_comp_comulAlgHom (θ a)) (x : H)).symm
    rw [hΔ, ← AlgHom.comp_apply, hcomp, AlgHom.comp_apply, hx, Algebra.TensorProduct.map_tmul, map_one]
  let θQ : κ → (↥(HopfAlgebra.hopfKer π) →ₐ[GaloisRep.ratLocalizedAt p] ↥(HopfAlgebra.hopfKer π)) := fun a =>
    AlgHom.codRestrict ((θ a : H →ₐ[GaloisRep.ratLocalizedAt p] H).comp (HopfAlgebra.hopfKer π).val)
      (HopfAlgebra.hopfKer π) (fun x => hmem a x)
  have hθQ : ∀ (a : κ) (x : ↥(HopfAlgebra.hopfKer π)), ((θQ a x : ↥(HopfAlgebra.hopfKer π)) : H) = θ a (x : H) :=
    fun a x => rfl
  refine ⟨θQ, hθQ, ?_⟩
  intro a f g hfg
  obtain ⟨ν, hν⟩ := hres (WithConv.ofConv f)
  let ν' : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) :=
    WithConv.toConv (ν.comp (θ a : H →ₐ[GaloisRep.ratLocalizedAt p] H))
  have hf : WithConv.toConv ((WithConv.ofConv (WithConv.toConv ν)).comp (HopfAlgebra.hopfKer π).val) = f := by
    rw [WithConv.ofConv_toConv, hν, WithConv.toConv_ofConv]
  have hg : WithConv.toConv ((WithConv.ofConv ν').comp (HopfAlgebra.hopfKer π).val) = g := by
    apply congrArg WithConv.toConv ∘ id
    apply AlgHom.ext
    intro h
    show ν (θ a (h : H)) = g h
    rw [hfg h, ← hf]
    rfl
  rw [← hg, heQ_res, ← hf, heQ_res, ← Submodule.Quotient.mk_smul]
  congr 1
  exact hθ a (WithConv.toConv ν) ν' (fun h => rfl)

set_option maxHeartbeats 3200000 in

theorem range_baseChange_hopfKer_val_eq_hopfKer
    (p : ℕ) [Fact p.Prime]
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Free (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    (HV : Type) [CommRing HV] [HopfAlgebra (GaloisRep.ratLocalizedAt p) HV]
    [Module.Finite (GaloisRep.ratLocalizedAt p) HV] [Module.Free (GaloisRep.ratLocalizedAt p) HV]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) HV] [Nontrivial HV]
    (π : H →ₐc[GaloisRep.ratLocalizedAt p] HV) (hπ : Function.Surjective π)
    [Module.Finite (GaloisRep.ratLocalizedAt p) ↥(HopfAlgebra.hopfKer π)]
    [Module.Free (GaloisRep.ratLocalizedAt p) ↥(HopfAlgebra.hopfKer π)]
    [Algebra (GaloisRep.ratLocalizedAt p) (ZMod p)] :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (HopfAlgebra.hopfKer π).val) ∧
    (Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (HopfAlgebra.hopfKer π).val).range =
      HopfAlgebra.hopfKer (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) π) := by
  classical

  let O := GaloisRep.ratLocalizedAt p
  let k := ZMod p
  let K := HopfAlgebra.hopfKer π
  let vk := Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (HopfAlgebra.hopfKer π).val
  let πk : (ZMod p) ⊗[GaloisRep.ratLocalizedAt p] H →ₐc[ZMod p] (ZMod p) ⊗[GaloisRep.ratLocalizedAt p] HV :=
    Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) π

  obtain ⟨⟨r, hr⟩, -, -, hrank⟩ :=
    HopfAlgebra.exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective π hπ
  let rk : (ZMod p) ⊗[GaloisRep.ratLocalizedAt p] H →ₗ[ZMod p] (ZMod p) ⊗[GaloisRep.ratLocalizedAt p] ↥K :=
    (r.restrictScalars (GaloisRep.ratLocalizedAt p)).baseChange (ZMod p)
  have hret : ∀ z, rk (vk z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul c x =>
      show rk (c ⊗ₜ[GaloisRep.ratLocalizedAt p] ((HopfAlgebra.hopfKer π).val x)) = c ⊗ₜ x
      rw [LinearMap.baseChange_tmul, LinearMap.restrictScalars_apply, Subalgebra.coe_val, hr x]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hinj : Function.Injective vk := fun x y h => by
    have := congrArg rk h
    rwa [hret, hret] at this
  refine ⟨hinj, ?_⟩

  have hle : vk.range ≤ HopfAlgebra.hopfKer πk := by
    rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => show vk 0 ∈ HopfAlgebra.hopfKer πk; rw [map_zero]; exact Subalgebra.zero_mem _
    | tmul c x =>
      show vk (c ⊗ₜ x) ∈ HopfAlgebra.hopfKer πk
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Subalgebra.coe_val]
      exact HLG.tmul_mem_hopfKer_baseChange π c x.2
    | add x y hx hy => show vk (x + y) ∈ HopfAlgebra.hopfKer πk; rw [map_add]; exact Subalgebra.add_mem _ hx hy

  haveI hπk : Function.Surjective πk := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul c v =>
      obtain ⟨h, rfl⟩ := hπ v
      exact ⟨c ⊗ₜ h, by rw [Bialgebra.TensorProduct.map_tmul]; rfl⟩
    | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, map_add _ _ _⟩
  haveI : Module.Finite (ZMod p) ↥(HopfAlgebra.hopfKer πk) :=
    Module.Finite.of_injective (HopfAlgebra.hopfKer πk).val.toLinearMap Subtype.val_injective
  obtain ⟨-, -, -, hrankk⟩ :=
    HopfAlgebra.exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective πk hπk

  have h1 : Module.finrank (GaloisRep.ratLocalizedAt p) ↥K * Module.finrank (GaloisRep.ratLocalizedAt p) HV =
      Module.finrank (GaloisRep.ratLocalizedAt p) H := by
    have := hrank ⟨⊥, Ideal.isPrime_bot⟩
    rwa [Module.rankAtStalk_eq_finrank_of_free] at this

  have h2 : Module.finrank (ZMod p) ↥(HopfAlgebra.hopfKer πk) *
      Module.finrank (ZMod p) ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] HV) =
      Module.finrank (ZMod p) ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] H) := by
    have := hrankk ⟨⊥, Ideal.isPrime_bot⟩
    rwa [Module.rankAtStalk_eq_finrank_of_free] at this
  rw [Module.finrank_baseChange, Module.finrank_baseChange, ← h1] at h2
  have hHV : Module.finrank (GaloisRep.ratLocalizedAt p) HV ≠ 0 := by
    rw [Ne, Module.finrank_eq_zero_iff_of_free]
    exact not_subsingleton HV
  have h3 : Module.finrank (ZMod p) ↥(HopfAlgebra.hopfKer πk) = Module.finrank (GaloisRep.ratLocalizedAt p) ↥K :=
    Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hHV) h2

  have h4 : Module.finrank (ZMod p) ↥(Subalgebra.toSubmodule vk.range) =
      Module.finrank (GaloisRep.ratLocalizedAt p) ↥K := by
    have hrg : Subalgebra.toSubmodule vk.range = LinearMap.range vk.toLinearMap := by
      ext z; simp [AlgHom.mem_range, LinearMap.mem_range]
    rw [hrg, LinearMap.finrank_range_of_inj (f := vk.toLinearMap) hinj, Module.finrank_baseChange]
  apply Subalgebra.toSubmodule_injective
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [h4, ← h3]
  rfl

end HLBody

set_option autoImplicit false
open scoped TensorProduct

namespace HLBody

set_option maxHeartbeats 3200000 in

theorem exists_bialgEquiv_comp_eq_of_range_eq
    {k : Type} [Field k] {A₁ A₂ B : Type} [CommRing A₁] [CommRing A₂] [CommRing B]
    [Bialgebra k A₁] [Bialgebra k A₂] [Bialgebra k B]
    (j₁ : A₁ →ₐc[k] B) (j₂ : A₂ →ₐc[k] B) (h₁ : Function.Injective j₁) (h₂ : Function.Injective j₂)
    (hrange : (j₁ : A₁ →ₐ[k] B).range = (j₂ : A₂ →ₐ[k] B).range) :
    ∃ σ : A₁ ≃ₐc[k] A₂, ∀ x : A₁, j₂ (σ x) = j₁ x := by
  classical

  let e₁ : A₁ ≃ₐ[k] ↥(j₁ : A₁ →ₐ[k] B).range := AlgEquiv.ofInjective (j₁ : A₁ →ₐ[k] B) h₁
  let e₂ : A₂ ≃ₐ[k] ↥(j₂ : A₂ →ₐ[k] B).range := AlgEquiv.ofInjective (j₂ : A₂ →ₐ[k] B) h₂
  let σ₀ : A₁ ≃ₐ[k] A₂ := (e₁.trans (Subalgebra.equivOfEq _ _ hrange)).trans e₂.symm
  have hσ₀ : ∀ x : A₁, j₂ (σ₀ x) = j₁ x := by
    intro x
    have h2 : ∀ y : ↥(j₂ : A₂ →ₐ[k] B).range, (j₂ : A₂ →ₐ[k] B) (e₂.symm y) = (y : B) := by
      intro y
      have := AlgEquiv.ofInjective_apply (j₂ : A₂ →ₐ[k] B) h₂ (e₂.symm y)
      rw [AlgEquiv.apply_symm_apply] at this
      exact this.symm
    show (j₂ : A₂ →ₐ[k] B) (e₂.symm (Subalgebra.equivOfEq _ _ hrange (e₁ x))) = j₁ x
    rw [h2]
    rfl

  have hcounit : (Bialgebra.counitAlgHom k A₂).comp (σ₀ : A₁ →ₐ[k] A₂) = Bialgebra.counitAlgHom k A₁ := by
    apply AlgHom.ext
    intro x
    rw [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, Bialgebra.counitAlgHom_apply, AlgEquiv.coe_algHom,
      ← CoalgHomClass.counit_comp_apply j₂ (σ₀ x), hσ₀, CoalgHomClass.counit_comp_apply j₁ x]

  have hinjL : Function.Injective (TensorProduct.map (j₂ : A₂ →ₐ[k] B).toLinearMap (j₂ : A₂ →ₐ[k] B).toLinearMap) := by
    have hl : Function.Injective ((j₂ : A₂ →ₐ[k] B).toLinearMap.lTensor A₂) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ h₂
    have hr : Function.Injective ((j₂ : A₂ →ₐ[k] B).toLinearMap.rTensor B) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ h₂
    rw [← LinearMap.rTensor_comp_lTensor]
    exact hr.comp hl
  have hinj2 : Function.Injective (Algebra.TensorProduct.map (j₂ : A₂ →ₐ[k] B) (j₂ : A₂ →ₐ[k] B)) := by
    intro a b hab
    apply hinjL
    exact hab
  have hcomp : (j₂ : A₂ →ₐ[k] B).comp (σ₀ : A₁ →ₐ[k] A₂) = (j₁ : A₁ →ₐ[k] B) := AlgHom.ext hσ₀
  have hcomul : (Algebra.TensorProduct.map (σ₀ : A₁ →ₐ[k] A₂) (σ₀ : A₁ →ₐ[k] A₂)).comp (Bialgebra.comulAlgHom k A₁) =
      (Bialgebra.comulAlgHom k A₂).comp (σ₀ : A₁ →ₐ[k] A₂) := by
    apply AlgHom.ext
    intro x
    apply hinj2
    rw [AlgHom.comp_apply, AlgHom.comp_apply]

    have hR := AlgHom.congr_fun (BialgHom.map_comp_comulAlgHom j₂) ((σ₀ : A₁ →ₐ[k] A₂) x)
    have hL := AlgHom.congr_fun (BialgHom.map_comp_comulAlgHom j₁) x
    rw [AlgHom.comp_apply, AlgHom.comp_apply] at hR hL
    rw [hR, ← AlgHom.comp_apply (j₂ : A₂ →ₐ[k] B) (σ₀ : A₁ →ₐ[k] A₂) x, hcomp, ← hL,
      ← AlgHom.comp_apply (Algebra.TensorProduct.map (j₂ : A₂ →ₐ[k] B) (j₂ : A₂ →ₐ[k] B)),
      ← Algebra.TensorProduct.map_comp, hcomp]
  refine ⟨BialgEquiv.ofAlgEquiv σ₀ hcounit hcomul, fun x => ?_⟩
  rw [BialgEquiv.ofAlgEquiv_apply]
  exact hσ₀ x

theorem exists_bialgHom_coe_eq_of_comp_eq
    {R : Type} [CommRing R] {A B : Type} [CommRing A] [CommRing B] [Bialgebra R A] [Bialgebra R B]
    (π : A →ₐc[R] B) (hπ : Function.Surjective π)
    (φ : A →ₐc[R] A) (ψ : B →ₐ[R] B)
    (h : ψ.comp (π : A →ₐ[R] B) = (π : A →ₐ[R] B).comp (φ : A →ₐ[R] A)) :
    ∃ ψb : B →ₐc[R] B, (ψb : B →ₐ[R] B) = ψ := by
  have happ : ∀ a : A, ψ (π a) = π (φ a) := fun a => congrArg (fun f : A →ₐ[R] B => f a) h
  have hcounit : (Bialgebra.counitAlgHom R B).comp ψ = Bialgebra.counitAlgHom R B := by
    apply AlgHom.ext; intro x; obtain ⟨a, rfl⟩ := hπ x
    simp only [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, happ]
    rw [CoalgHomClass.counit_comp_apply π, CoalgHomClass.counit_comp_apply φ, CoalgHomClass.counit_comp_apply π]
  have hcomul : (Algebra.TensorProduct.map ψ ψ).comp (Bialgebra.comulAlgHom R B) =
      (Bialgebra.comulAlgHom R B).comp ψ := by
    apply AlgHom.ext; intro x; obtain ⟨a, rfl⟩ := hπ x
    simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, happ]
    rw [← CoalgHomClass.map_comp_comul_apply π a, ← CoalgHomClass.map_comp_comul_apply π (φ a),
      ← CoalgHomClass.map_comp_comul_apply φ a]
    induction (Coalgebra.comul (R := R) a) using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [happ]
    | add x y hx hy => simp only [map_add, hx, hy]
  exact ⟨BialgHom.ofAlgHom ψ hcounit hcomul, rfl⟩

end HLBody

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
open scoped TensorProduct
namespace HLBody

set_option maxHeartbeats 3200000 in

theorem theta_hopfKer_bialgHom
    (p : ℕ) [Fact p.Prime]
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Free (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    (HV : Type) [CommRing HV] [HopfAlgebra (GaloisRep.ratLocalizedAt p) HV]
    [Module.Finite (GaloisRep.ratLocalizedAt p) HV] [Module.Free (GaloisRep.ratLocalizedAt p) HV]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) HV]
    (π : H →ₐc[GaloisRep.ratLocalizedAt p] HV)
    [Module.Flat (GaloisRep.ratLocalizedAt p) ↥(HopfAlgebra.hopfKer π)]
    {κ : Type} (θ : κ → (H →ₐc[GaloisRep.ratLocalizedAt p] H))
    (θQ : κ → (↥(HopfAlgebra.hopfKer π) →ₐ[GaloisRep.ratLocalizedAt p] ↥(HopfAlgebra.hopfKer π)))
    (hθQ : ∀ (a : κ) (x : ↥(HopfAlgebra.hopfKer π)), ((θQ a x : ↥(HopfAlgebra.hopfKer π)) : H) = θ a (x : H)) :
    ∃ θQb : κ → (↥(HopfAlgebra.hopfKer π) →ₐc[GaloisRep.ratLocalizedAt p] ↥(HopfAlgebra.hopfKer π)),
      ∀ (a : κ) (x : ↥(HopfAlgebra.hopfKer π)), θQb a x = θQ a x := by
  classical
  haveI : Module.Flat (GaloisRep.ratLocalizedAt p) H := Module.Flat.of_free
  haveI : Module.Flat (GaloisRep.ratLocalizedAt p) HV := Module.Flat.of_free
  have hb : ∀ a : κ, ∃ θQb : ↥(HopfAlgebra.hopfKer π) →ₐc[GaloisRep.ratLocalizedAt p] ↥(HopfAlgebra.hopfKer π),
      ∀ x, θQb x = θQ a x := by
    intro a

    have hcounit : (Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) ↥(HopfAlgebra.hopfKer π)).comp (θQ a) =
        Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) ↥(HopfAlgebra.hopfKer π) := by
      apply AlgHom.ext
      intro x
      rw [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, Bialgebra.counitAlgHom_apply,
        HopfAlgebra.counit_coe, HopfAlgebra.counit_coe, hθQ]
      exact CoalgHomClass.counit_comp_apply (θ a) (x : H)

    have hcomul : (Algebra.TensorProduct.map (θQ a) (θQ a)).comp
          (Bialgebra.comulAlgHom (GaloisRep.ratLocalizedAt p) ↥(HopfAlgebra.hopfKer π)) =
        (Bialgebra.comulAlgHom (GaloisRep.ratLocalizedAt p) ↥(HopfAlgebra.hopfKer π)).comp (θQ a) := by
      apply AlgHom.ext
      intro x
      apply HopfAlgebra.HopfKerHopf.ι₂_injective π
      rw [AlgHom.comp_apply, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, Bialgebra.comulAlgHom_apply,
        HopfAlgebra.HopfKerHopf.ι₂_comul]

      have hsq : ∀ z : ↥(HopfAlgebra.hopfKer π) ⊗[GaloisRep.ratLocalizedAt p] ↥(HopfAlgebra.hopfKer π),
          HopfAlgebra.HopfKerHopf.ι₂ π (Algebra.TensorProduct.map (θQ a) (θQ a) z) =
            Algebra.TensorProduct.map (θ a : H →ₐ[GaloisRep.ratLocalizedAt p] H) (θ a : H →ₐ[GaloisRep.ratLocalizedAt p] H)
              (HopfAlgebra.HopfKerHopf.ι₂ π z) := by
        intro z
        induction z using TensorProduct.induction_on with
        | zero => rw [map_zero, map_zero, map_zero]
        | tmul s t =>
          rw [Algebra.TensorProduct.map_tmul, HopfAlgebra.HopfKerHopf.ι₂_tmul, HopfAlgebra.HopfKerHopf.ι₂_tmul,
            Algebra.TensorProduct.map_tmul, hθQ, hθQ]
          rfl
        | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]
      rw [hsq, HopfAlgebra.HopfKerHopf.ι₂_comul, hθQ]
      exact CoalgHomClass.map_comp_comul_apply (θ a) (x : H)
    exact ⟨BialgHom.ofAlgHom (θQ a) hcounit hcomul, fun x => rfl⟩
  choose θQb hθQb using hb
  exact ⟨θQb, hθQb⟩

end HLBody

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct

namespace HLBody

@[reducible] noncomputable def subAction {κ N : Type} [Field κ] [AddCommGroup N] [Module κ N]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (N →ₗ[κ] N))
    (V : Submodule κ N) (hV : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ∀ x ∈ V, ρ σ x ∈ V) :
    DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ↥V where
  smul σ v := ⟨ρ σ v, hV σ v v.2⟩
  one_smul v := Subtype.ext (by show ρ 1 v = v; rw [map_one]; rfl)
  mul_smul σ τ v := Subtype.ext (by show ρ (σ * τ) v = ρ σ (ρ τ v); rw [map_mul]; rfl)
  smul_zero σ := Subtype.ext (by show ρ σ (0 : ↥V) = 0; exact map_zero _)
  smul_add σ v w := Subtype.ext (by show ρ σ ((v : N) + w) = ρ σ v + ρ σ w; exact map_add _ _ _)

end HLBody

set_option maxHeartbeats 8000000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Free (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    (hloc : IsLocalRing H) (hdual : IsLocalRing (CartierDual (GaloisRep.ratLocalizedAt p) H))
    {κ : Type} [Field κ] [Finite κ] [CharP κ p]
    {N : Type} [AddCommGroup N] [Module κ N] [Module.Finite κ N]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (N →ₗ[κ] N))
    (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ N)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_gal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ h : H, g h = σ (f h)) → e g = ρ σ (e f))
    (θ : κ → (H →ₐc[GaloisRep.ratLocalizedAt p] H))
    (hθ : ∀ (a : κ) (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ h : H, g h = f (θ a h)) → e g = a • e f)
    (V : Submodule κ N)
    (hV : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ∀ x ∈ V, ρ σ x ∈ V)
    (HV : Type) [CommRing HV] [HopfAlgebra (GaloisRep.ratLocalizedAt p) HV]
    [Module.Finite (GaloisRep.ratLocalizedAt p) HV] [Module.Free (GaloisRep.ratLocalizedAt p) HV]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) HV]
    (π : H →ₐc[GaloisRep.ratLocalizedAt p] HV) (hπ : Function.Surjective π)
    (eV : WithConv (HV →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ ↥V)
    (heV : ∀ f : WithConv (HV →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
      ((eV f : ↥V) : N) =
        e (WithConv.toConv ((WithConv.ofConv f).comp (π : H →ₐ[GaloisRep.ratLocalizedAt p] HV))))
    (θV : κ → (HV →ₐc[GaloisRep.ratLocalizedAt p] HV))
    (hθV : ∀ a : κ,
      (θV a : HV →ₐ[GaloisRep.ratLocalizedAt p] HV).comp (π : H →ₐ[GaloisRep.ratLocalizedAt p] HV) =
        (π : H →ₐ[GaloisRep.ratLocalizedAt p] HV).comp (θ a : H →ₐ[GaloisRep.ratLocalizedAt p] H))
    (hbot : V ≠ ⊤ →
      ∃ (V' : Submodule κ (N ⧸ V)) (ι : ↥V ≃ₗ[κ] ↥V'),
        (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ∀ x ∈ V',
          Submodule.mapQ V V (ρ σ) (fun y hy => hV σ y hy) x ∈ V') ∧
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : ↥V),
          ((ι ⟨ρ σ v, hV σ v v.2⟩ : ↥V') : N ⧸ V) =
            Submodule.mapQ V V (ρ σ) (fun y hy => hV σ y hy) ((ι v : ↥V') : N ⧸ V))
    (hVtop : V ≠ ⊤) :
    ∃ lam : ↥(AddMonoidHom.ker (Deformation.DieudonneModule.map (ZMod p) p
          (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) π))) →+
        Deformation.DieudonneModule (ZMod p) p ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] HV),
      Function.Surjective lam ∧
      (∀ x (hx : Deformation.DieudonneModule.frobenius (ZMod p) p _ x.1 ∈
          AddMonoidHom.ker (Deformation.DieudonneModule.map (ZMod p) p
            (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) π))),
        lam ⟨_, hx⟩ = Deformation.DieudonneModule.frobenius (ZMod p) p _ (lam x)) ∧
      (∀ x (hx : Deformation.DieudonneModule.verschiebung (ZMod p) p _ x.1 ∈
          AddMonoidHom.ker (Deformation.DieudonneModule.map (ZMod p) p
            (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) π))),
        lam ⟨_, hx⟩ = Deformation.DieudonneModule.verschiebung (ZMod p) p _ (lam x)) ∧
      (∀ (a : κ) x (hx : Deformation.DieudonneModule.map (ZMod p) p
            (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (θ a)) x.1 ∈
          AddMonoidHom.ker (Deformation.DieudonneModule.map (ZMod p) p
            (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) π))),
        lam ⟨_, hx⟩ = Deformation.DieudonneModule.map (ZMod p) p
          (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (θV a)) (lam x)) := by
  classical
  haveI hlocZ : IsLocalRing (GaloisRep.ratLocalizedAt p) := GaloisRep.ratLocalizedAt.isLocalRing Fact.out
  obtain ⟨V', ι, hV'gal, hιgal⟩ := hbot hVtop

  obtain ⟨_, hfinQ, hprojQ, _⟩ := HopfAlgebra.exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective π hπ
  haveI := hfinQ
  haveI := hprojQ
  haveI hfreeQ : Module.Free (GaloisRep.ratLocalizedAt p) ↥(HopfAlgebra.hopfKer π) := Module.free_of_flat_of_isLocalRing
  haveI : Nontrivial HV := (WithConv.ofConv (eV.symm 0)).toRingHom.domain_nontrivial
  obtain ⟨hlocQ, hdualQ⟩ :=
    HopfAlgebra.isLocalRing_hopfKer_and_isLocalRing_cartierDual_hopfKer_of_surjective (GaloisRep.ratLocalizedAt p)
      H HV π hπ hloc hdual

  obtain ⟨eQ, heQ_add, heQ_gal, heQ_res, hres⟩ :=
    HLBody.points_hopfKer p H HV π hπ ρ e he_add he_gal V hV eV heV
  obtain ⟨θQ, hθQval, hθQpt⟩ :=
    HLBody.theta_hopfKer p H HV π hπ e θ hθ θV hθV V eQ heQ_res hres

  letI := HLBody.quotAction ρ V hV
  have hV'gal' : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ∀ x ∈ V'.toAddSubgroup, σ • x ∈ V'.toAddSubgroup :=
    fun σ x hx => hV'gal σ x hx
  have hV'act : ∀ a : κ, ∀ x ∈ V'.toAddSubgroup, DistribSMul.toAddMonoidHom (N ⧸ V) a x ∈ V'.toAddSubgroup :=
    fun a x hx => V'.smul_mem a hx
  obtain ⟨HQ', _i1, _i2, _i3, _i4, _i5, π', eQ', θQ', hπ', heQ', hθQ'⟩ :=
    GaloisRep.exists_bialgHom_surjective_finiteFlat_model_addSubgroup_of_stable p ↥(HopfAlgebra.hopfKer π)
      eQ heQ_add (fun σ f g hfg => by rw [heQ_gal σ f g hfg]; rfl)
      (T := κ) (fun a => DistribSMul.toAddMonoidHom (N ⧸ V) a) θQ
      (fun a f g hfg => by rw [hθQpt a f g hfg]; rfl) V'.toAddSubgroup hV'gal' hV'act

  letI := HLBody.subAction ρ V hV
  have hrank_of : ∀ (A : Type) [CommRing A] [HopfAlgebra (GaloisRep.ratLocalizedAt p) A]
      [Module.Finite (GaloisRep.ratLocalizedAt p) A] [Module.Free (GaloisRep.ratLocalizedAt p) A]
      [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) A],
      IsLocalRing (CartierDual (GaloisRep.ratLocalizedAt p) A) →
        ∃ a : ℕ, Module.finrank (GaloisRep.ratLocalizedAt p) A = p ^ a := by
    intro A _ _ _ _ _ hA
    have hunipA : IsLocalRing (CartierDual (ZMod p) ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A)) :=
      (CartierDual.isLocalRing_baseChange_and_isLocalRing_cartierDual_baseChange p A (ZMod p)).2 hA
    obtain ⟨a, ha, _⟩ :=
      Deformation.DieudonneModule.exists_finrank_eq_pow_and_natCard_eq_pow_of_isLocalRing_cartierDual
        (ZMod p) p ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] A) hunipA
    exact ⟨a, by rw [← ha, Module.finrank_baseChange]⟩
  have hdualV : IsLocalRing (CartierDual (GaloisRep.ratLocalizedAt p) HV) :=
    CartierDual.isLocalRing_cartierDual_of_bialgHom_surjective (GaloisRep.ratLocalizedAt p) H HV π hπ hdual
  have hrankHV : ∃ a : ℕ, Module.finrank (GaloisRep.ratLocalizedAt p) HV = p ^ a := hrank_of HV hdualV
  haveI : Nontrivial HQ' := (WithConv.ofConv (eQ'.symm ⟨(ι 0 : ↥V'), (ι 0).2⟩)).toRingHom.domain_nontrivial
  have hdualQ' : IsLocalRing (CartierDual (GaloisRep.ratLocalizedAt p) HQ') :=
    CartierDual.isLocalRing_cartierDual_of_bialgHom_surjective (GaloisRep.ratLocalizedAt p)
      ↥(HopfAlgebra.hopfKer π) HQ' π' hπ' hdualQ
  have hrankHQ' : ∃ a : ℕ, Module.finrank (GaloisRep.ratLocalizedAt p) HQ' = p ^ a := hrank_of HQ' hdualQ'
  have heV_add : ∀ f g, eV (f * g) = eV f + eV g := by
    intro f g
    apply Subtype.ext
    rw [Submodule.coe_add, heV, heV, heV, ← he_add]
    congr 1
    rw [AlgHom.convMul_comp_bialgHom_distrib]
  have heV_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (HV →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ x : HV, g x = σ (f x)) → eV g = σ • eV f := by
    intro σ f g hfg
    apply Subtype.ext
    show ((eV g : ↥V) : N) = ρ σ ((eV f : ↥V) : N)
    rw [heV, heV]
    exact he_gal σ _ _ (fun h => hfg (π h))
  let e₂ : WithConv (HQ' →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ ↥V :=
    eQ'.trans ((Equiv.refl _).trans ι.symm.toEquiv)
  have heQ'_add : ∀ f g, eQ' (f * g) = eQ' f + eQ' g := by
    intro f g
    apply Subtype.ext
    rw [AddSubgroup.coe_add]
    show ((eQ' (f * g) : ↥V'.toAddSubgroup) : N ⧸ V) = ((eQ' f : ↥V'.toAddSubgroup) : N ⧸ V) + ((eQ' g : ↥V'.toAddSubgroup) : N ⧸ V)
    rw [heQ', heQ', heQ', ← heQ_add]
    congr 1
    rw [AlgHom.convMul_comp_bialgHom_distrib]
  have he₂ : ∀ f, e₂ f = ι.symm ⟨((eQ' f : ↥V'.toAddSubgroup) : N ⧸ V), (eQ' f).2⟩ := fun _ => rfl
  have he₂_add : ∀ f g, e₂ (f * g) = e₂ f + e₂ g := by
    intro f g
    rw [he₂, he₂, he₂, ← map_add]
    congr 1
    apply Subtype.ext
    show ((eQ' (f * g) : ↥V'.toAddSubgroup) : N ⧸ V) = _
    rw [heQ'_add]; rfl
  have he₂_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (HQ' →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ x : HQ', g x = σ (f x)) → e₂ g = σ • e₂ f := by
    intro σ f g hfg
    rw [he₂, he₂]
    apply ι.injective
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext

    have h1 : ((eQ' g : ↥V'.toAddSubgroup) : N ⧸ V) =
        Submodule.mapQ V V (ρ σ) (fun y hy => hV σ y hy) ((eQ' f : ↥V'.toAddSubgroup) : N ⧸ V) := by
      rw [heQ', heQ']
      exact heQ_gal σ _ _ (fun h => hfg (π' h))
    rw [h1]
    show _ = ((ι (σ • ι.symm ⟨((eQ' f : ↥V'.toAddSubgroup) : N ⧸ V), (eQ' f).2⟩) : ↥V') : N ⧸ V)
    have h2 := hιgal σ (ι.symm ⟨((eQ' f : ↥V'.toAddSubgroup) : N ⧸ V), (eQ' f).2⟩)

    rw [LinearEquiv.apply_symm_apply] at h2
    exact h2.symm.trans (by rfl)
  obtain ⟨⟨g, hg, hguniq⟩, hgbij⟩ :=
    HopfAlgebra.existsUnique_bialgHom_ratLocalizedAt_forall_apply_comp_eq_and_bijective_of_addEquiv_of_ne_two
      p hp2 HV hrankHV eV heV_add heV_act HQ' hrankHQ' e₂ he₂_add he₂_act (AddEquiv.refl ↥V) (fun σ m => rfl)
  have hgb : Function.Bijective g := hgbij g hg

  haveI : Module.Flat (GaloisRep.ratLocalizedAt p) ↥(HopfAlgebra.hopfKer π) := inferInstance

  obtain ⟨θQb, hθQb⟩ := HLBody.theta_hopfKer_bialgHom p H HV π θ θQ hθQval
  have hθQ'b : ∀ a : κ, ∃ ψb : HQ' →ₐc[GaloisRep.ratLocalizedAt p] HQ', (ψb : HQ' →ₐ[GaloisRep.ratLocalizedAt p] HQ') = θQ' a := by
    intro a
    refine HLBody.exists_bialgHom_coe_eq_of_comp_eq π' hπ' (θQb a) (θQ' a) ?_
    rw [hθQ' a]; congr 1; apply AlgHom.ext; intro x; exact (hθQb a x).symm ▸ rfl
  choose θQ'b hθQ'b_coe using hθQ'b

  let valb := Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (HopfAlgebra.hopfKerVal π)
  let πb := Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) π
  let π'b := Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) π'
  let gb := Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) g
  let Mval := Deformation.DieudonneModule.map (ZMod p) p valb
  let Mπ := Deformation.DieudonneModule.map (ZMod p) p πb
  let Mw := (Deformation.DieudonneModule.map (ZMod p) p gb).comp (Deformation.DieudonneModule.map (ZMod p) p π'b)

  have hkerres : RingHom.ker (algebraMap (GaloisRep.ratLocalizedAt p) (ZMod p)) =
      Ideal.span {((p : ℕ) : GaloisRep.ratLocalizedAt p)} := by
    rw [← GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast p Fact.out]
    haveI := RingHom.ker_isMaximal_of_surjective (algebraMap (GaloisRep.ratLocalizedAt p) (ZMod p))
      (ZMod.ringHom_surjective _)
    exact IsLocalRing.eq_maximalIdeal inferInstance
  have hpnzd : ((p : ℕ) : GaloisRep.ratLocalizedAt p) ∈ nonZeroDivisors (GaloisRep.ratLocalizedAt p) := by
    apply mem_nonZeroDivisors_of_ne_zero; exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hunipH : IsLocalRing (CartierDual (ZMod p) ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] H)) :=
    (CartierDual.isLocalRing_baseChange_and_isLocalRing_cartierDual_baseChange p H (ZMod p)).2 hdual
  obtain ⟨-, hMval_inj, hcomp0, -, -⟩ :=
    Deformation.DieudonneModule.map_baseChange_surjective_injective_fontaineHodge_of_range_eq_hopfKer
      p hpnzd hkerres H (hrank_of H hdual) hunipH HV hrankHV ↥(HopfAlgebra.hopfKer π) π hπ
      (HopfAlgebra.hopfKerVal π) (HopfAlgebra.hopfKerVal_injective π) (by ext x; simp [HopfAlgebra.hopfKerVal_apply])

  have hexact : ∀ x, Mπ x = 0 → ∃ y, Mval y = x := by
    intro x hx
    have hE := Deformation.DieudonneModule.exact_map_hopfKerVal_map (ZMod p) p πb
    obtain ⟨z, hz⟩ := (hE x).mp hx
    obtain ⟨hinjv, hrangev⟩ := HLBody.range_baseChange_hopfKer_val_eq_hopfKer p H HV π hπ
    have hinjv' : Function.Injective valb := hinjv
    have hrange' : (valb : (ZMod p) ⊗[GaloisRep.ratLocalizedAt p] ↥(HopfAlgebra.hopfKer π) →ₐ[ZMod p]
        (ZMod p) ⊗[GaloisRep.ratLocalizedAt p] H).range =
        (HopfAlgebra.hopfKerVal πb : ↥(HopfAlgebra.hopfKer πb) →ₐ[ZMod p] (ZMod p) ⊗[GaloisRep.ratLocalizedAt p] H).range := by
      rw [show (HopfAlgebra.hopfKerVal πb : ↥(HopfAlgebra.hopfKer πb) →ₐ[ZMod p] _) = (HopfAlgebra.hopfKer πb).val from rfl,
        Subalgebra.range_val]
      exact hrangev
    obtain ⟨σ, hσ⟩ := HLBody.exists_bialgEquiv_comp_eq_of_range_eq valb (HopfAlgebra.hopfKerVal πb) hinjv'
      (HopfAlgebra.hopfKerVal_injective πb) hrange'
    have hcompσ : (HopfAlgebra.hopfKerVal πb).comp σ.toBialgHom = valb := by
      apply BialgHom.coe_algHom_injective; apply AlgHom.ext; intro y
      show HopfAlgebra.hopfKerVal πb (σ y) = valb y
      exact hσ y
    refine ⟨Deformation.DieudonneModule.map (ZMod p) p σ.symm.toBialgHom z, ?_⟩
    show Deformation.DieudonneModule.map (ZMod p) p valb _ = x
    have hσσ : (σ.toBialgHom.comp σ.symm.toBialgHom) = BialgHom.id (ZMod p) _ := by
      apply BialgHom.coe_algHom_injective; apply AlgHom.ext; intro y
      show σ (σ.symm y) = y
      exact σ.apply_symm_apply y
    rw [← hcompσ, Deformation.DieudonneModule.map_comp,
      ← Deformation.DieudonneModule.map_comp σ.symm.toBialgHom σ.toBialgHom z, hσσ, Deformation.DieudonneModule.map_id]
    exact hz

  have hlift : ∀ x : ↥(AddMonoidHom.ker Mπ), ∃! y, Mval y = x.1 := fun x => by
    obtain ⟨y, hy⟩ := hexact x.1 x.2
    exact ⟨y, hy, fun y' hy' => hMval_inj (hy'.trans hy.symm)⟩
  choose jf hjf hjf_uniq using hlift
  have hj_char : ∀ (x : ↥(AddMonoidHom.ker Mπ)) (y), Mval y = x.1 → jf x = y :=
    fun x y hy => (hjf_uniq x y hy).symm ▸ rfl
  let j : ↥(AddMonoidHom.ker Mπ) →+ Deformation.DieudonneModule (ZMod p) p ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] ↥(HopfAlgebra.hopfKer π)) :=
    { toFun := jf
      map_zero' := hj_char 0 0 (by rw [map_zero]; rfl)
      map_add' := fun x y => hj_char (x + y) (jf x + jf y) (by rw [map_add, hjf, hjf]; rfl) }
  have hj : ∀ x, j x = jf x := fun _ => rfl
  have hj_surj : Function.Surjective j := by
    intro y
    refine ⟨⟨Mval y, ?_⟩, ?_⟩
    · exact hcomp0 y
    · exact hj_char _ y rfl

  let lam : ↥(AddMonoidHom.ker Mπ) →+ Deformation.DieudonneModule (ZMod p) p ((ZMod p) ⊗[GaloisRep.ratLocalizedAt p] HV) :=
    Mw.comp j
  have hlam : ∀ x, lam x = Deformation.DieudonneModule.map (ZMod p) p gb (Deformation.DieudonneModule.map (ZMod p) p π'b (jf x)) :=
    fun _ => rfl

  haveI : Nontrivial HQ' := inferInstance
  have hbc_surj : ∀ {A B : Type} [CommRing A] [CommRing B] [Bialgebra (GaloisRep.ratLocalizedAt p) A]
      [Bialgebra (GaloisRep.ratLocalizedAt p) B] (f : A →ₐc[GaloisRep.ratLocalizedAt p] B),
      Function.Surjective f →
        Function.Surjective (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) f) := by
    intro A B _ _ _ _ f hf z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul c b =>
      obtain ⟨a, rfl⟩ := hf b
      exact ⟨c ⊗ₜ a, rfl⟩
    | add x y hx hy =>
      obtain ⟨x', rfl⟩ := hx; obtain ⟨y', rfl⟩ := hy
      exact ⟨x' + y', map_add _ _ _⟩
  have hπ'b_surj : Function.Surjective π'b := hbc_surj π' hπ'
  have hgb_surj : Function.Surjective gb := hbc_surj g hgb.2
  have hMw_surj : Function.Surjective Mw :=
    (Deformation.DieudonneModule.map_surjective_of_surjective (ZMod p) p gb hgb_surj).comp
      (Deformation.DieudonneModule.map_surjective_of_surjective (ZMod p) p π'b hπ'b_surj)
  refine ⟨lam, hMw_surj.comp hj_surj, ?_, ?_, ?_⟩
  ·
    intro x hx
    rw [hlam, hlam]
    have : jf ⟨_, hx⟩ = Deformation.DieudonneModule.frobenius (ZMod p) p _ (jf x) :=
      hj_char ⟨_, hx⟩ _ (by rw [Deformation.DieudonneModule.map_frobenius, hjf])
    rw [this, Deformation.DieudonneModule.map_frobenius, Deformation.DieudonneModule.map_frobenius]
  ·
    intro x hx
    rw [hlam, hlam]
    have : jf ⟨_, hx⟩ = Deformation.DieudonneModule.verschiebung (ZMod p) p _ (jf x) :=
      hj_char ⟨_, hx⟩ _ (by rw [Deformation.DieudonneModule.map_verschiebung, hjf])
    rw [this, Deformation.DieudonneModule.map_verschiebung, Deformation.DieudonneModule.map_verschiebung]
  ·
    intro a x hx
    have hbc_comp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
        [Bialgebra (GaloisRep.ratLocalizedAt p) A] [Bialgebra (GaloisRep.ratLocalizedAt p) B]
        [Bialgebra (GaloisRep.ratLocalizedAt p) C]
        (f : B →ₐc[GaloisRep.ratLocalizedAt p] C) (g' : A →ₐc[GaloisRep.ratLocalizedAt p] B),
        Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (f.comp g') =
          (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) f).comp
            (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) g') := by
      intro A B C _ _ _ _ _ _ f g'
      apply BialgHom.coe_algHom_injective; apply AlgHom.toLinearMap_injective
      apply TensorProduct.AlgebraTensorModule.ext; intro u v; rfl

    have h1 : (HopfAlgebra.hopfKerVal π).comp (θQb a) = (θ a).comp (HopfAlgebra.hopfKerVal π) := by
      apply BialgHom.coe_algHom_injective; apply AlgHom.ext; intro q
      show ((θQb a q : ↥(HopfAlgebra.hopfKer π)) : H) = θ a (q : H)
      rw [hθQb]; exact hθQval a q
    have hj1 : jf ⟨_, hx⟩ = Deformation.DieudonneModule.map (ZMod p) p
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (θQb a)) (jf x) := by
      apply hj_char
      show Deformation.DieudonneModule.map (ZMod p) p valb _ = _
      rw [← Deformation.DieudonneModule.map_comp]
      show Deformation.DieudonneModule.map (ZMod p) p
        ((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (HopfAlgebra.hopfKerVal π)).comp
          (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (θQb a))) (jf x) = _
      rw [← hbc_comp, h1, hbc_comp, Deformation.DieudonneModule.map_comp]
      show Deformation.DieudonneModule.map (ZMod p) p _ (Deformation.DieudonneModule.map (ZMod p) p valb (jf x)) = _
      rw [hjf]

    have h2 : π'.comp (θQb a) = (θQ'b a).comp π' := by
      apply BialgHom.coe_algHom_injective; apply AlgHom.ext; intro q
      show π' (θQb a q) = θQ'b a (π' q)
      rw [hθQb, show θQ'b a (π' q) = θQ' a (π' q) from
        congrArg (fun f : HQ' →ₐ[GaloisRep.ratLocalizedAt p] HQ' => f (π' q)) (hθQ'b_coe a)]
      exact (congrArg (fun f : ↥(HopfAlgebra.hopfKer π) →ₐ[GaloisRep.ratLocalizedAt p] HQ' => f q) (hθQ' a)).symm

    have hθVapp : ∀ h : H, θV a (π h) = π (θ a h) := fun h =>
      congrArg (fun f : H →ₐ[GaloisRep.ratLocalizedAt p] HV => f h) (hθV a)
    have hθVpt : ∀ (f g' : WithConv (HV →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
        (∀ h : HV, g' h = f (θV a h)) → eV g' = a • eV f := by
      intro f g' hfg
      apply Subtype.ext
      rw [Submodule.coe_smul, heV, heV]
      exact hθ a _ _ (fun h => by show g' (π h) = f (π (θ a h)); rw [hfg, hθVapp])
    have hθQ'pt : ∀ φ : WithConv (HQ' →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        e₂ (WithConv.toConv ((WithConv.ofConv φ).comp (θQ'b a : HQ' →ₐ[GaloisRep.ratLocalizedAt p] HQ'))) = a • e₂ φ := by
      intro φ
      rw [he₂, he₂, ← LinearEquiv.map_smul]
      congr 1
      apply Subtype.ext
      show ((eQ' _ : ↥V'.toAddSubgroup) : N ⧸ V) = a • ((eQ' φ : ↥V'.toAddSubgroup) : N ⧸ V)
      rw [heQ', heQ']
      have hcomp : ((WithConv.ofConv φ).comp (θQ'b a : HQ' →ₐ[GaloisRep.ratLocalizedAt p] HQ')).comp
          (π' : ↥(HopfAlgebra.hopfKer π) →ₐ[GaloisRep.ratLocalizedAt p] HQ') =
          ((WithConv.ofConv φ).comp (π' : ↥(HopfAlgebra.hopfKer π) →ₐ[GaloisRep.ratLocalizedAt p] HQ')).comp (θQ a) := by
        rw [AlgHom.comp_assoc, hθQ'b_coe a, hθQ' a, ← AlgHom.comp_assoc]
      rw [hcomp]
      exact hθQpt a (WithConv.toConv ((WithConv.ofConv φ).comp (π' : ↥(HopfAlgebra.hopfKer π) →ₐ[GaloisRep.ratLocalizedAt p] HQ'))) _
        (fun h => rfl)
    have h3 : g.comp (θQ'b a) = (θV a).comp g := by
      apply BialgHom.coe_algHom_injective; apply AlgHom.ext; intro q'
      show g (θQ'b a q') = θV a (g q')
      apply HopfAlgebra.eq_of_forall_algHom_algebraicClosure_apply_eq_of_flat_ratLocalizedAt p HV
      intro f
      have key : WithConv.toConv (((f.comp (g : HQ' →ₐ[GaloisRep.ratLocalizedAt p] HV)).comp
            (θQ'b a : HQ' →ₐ[GaloisRep.ratLocalizedAt p] HQ'))) =
          WithConv.toConv ((f.comp (θV a : HV →ₐ[GaloisRep.ratLocalizedAt p] HV)).comp
            (g : HQ' →ₐ[GaloisRep.ratLocalizedAt p] HV)) := by
        apply e₂.injective
        have hL := hθQ'pt (WithConv.toConv (f.comp (g : HQ' →ₐ[GaloisRep.ratLocalizedAt p] HV)))
        rw [WithConv.ofConv_toConv] at hL
        rw [hL]
        have hgf := hg (WithConv.toConv f)
        have hgfθ := hg (WithConv.toConv (f.comp (θV a : HV →ₐ[GaloisRep.ratLocalizedAt p] HV)))
        rw [WithConv.ofConv_toConv] at hgf hgfθ
        rw [hgf, hgfθ]
        show a • eV (WithConv.toConv f) = eV (WithConv.toConv (f.comp (θV a : HV →ₐ[GaloisRep.ratLocalizedAt p] HV)))
        exact (hθVpt _ _ (fun h => rfl)).symm
      exact congrArg (fun φ : WithConv (HQ' →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) => WithConv.ofConv φ q') key

    rw [hlam, hlam, hj1, ← Deformation.DieudonneModule.map_comp
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (θQb a)) π'b,
      show π'b.comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (θQb a)) =
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (θQ'b a)).comp π'b from by
          show (Bialgebra.TensorProduct.map _ π').comp _ = _
          rw [← hbc_comp, h2, hbc_comp],
      Deformation.DieudonneModule.map_comp, ← Deformation.DieudonneModule.map_comp
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (θQ'b a)) gb,
      show gb.comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (θQ'b a)) =
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (θV a)).comp gb from by
          show (Bialgebra.TensorProduct.map _ g).comp _ = _
          rw [← hbc_comp, h3, hbc_comp],
      Deformation.DieudonneModule.map_comp]

end S_Deformation_DieudonneModule_exists_surjective_ker_map_of_bottomLayer
end P2MW
export P2MW.S_Deformation_DieudonneModule_exists_surjective_ker_map_of_bottomLayer (solution)
