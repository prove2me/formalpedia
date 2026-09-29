-- Prove2me | solution 1 for CuspForm.TWLevel.HeckeRing.OperatorAlgebra.exists_U_eigenvector_H1_of_algHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/3e197d35-90d4-5600-b29a-89242221b4da

import Definitions.Def_CuspForm_TWLevelHeckeRing
import Theorems.Thm_CohCarrier_H1_moduleFinite
import Theorems.Thm_CohCarrier_heckeT_comp_coeff
import Theorems.Thm_CohCarrier_HeckeData_finite_ML_and_free_ML
import Theorems.Thm_DeligneSerre_OperatorAlgebra_exists_eigenvector_baseChange_of_algHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_TWLevel_HeckeRing_OperatorAlgebra_exists_U_eigenvector_H1_of_algHom
p2m_attr_erase "instance" "IharaLemma.IdempotentSplitting.isScalarTower_base_cornerModule IharaLemma.IdempotentSplitting.isScalarTower_base_cornerRing IharaLemma.IdempotentSplitting.algebraBaseCornerRing IharaLemma.IdempotentSplitting.smulCornerModule IharaLemma.IdempotentSplitting.moduleCornerModule IharaLemma.IdempotentSplitting.isLocalRing_cornerRing IharaLemma.IdempotentSplitting.coeOutCornerRing IharaLemma.IdempotentSplitting.isMaximal_𝔪 IharaLemma.IdempotentSplitting.isScalarTower_cornerModule IharaLemma.IdempotentSplitting.isLocalization_cornerRing"
p2m_attr_erase "simp" "IharaLemma.IdempotentSplitting.cornerRingLinearEquiv_apply IharaLemma.IdempotentSplitting.cornerRingLinearEquiv_symm_apply IharaLemma.IdempotentSplitting.coe_cornerSmul IharaLemma.IdempotentSplitting.mk.injEq IharaLemma.IdempotentSplitting.mk.sizeOf_spec IharaLemma.IdempotentSplitting.coe_toCornerRing IharaLemma.toCorner_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open scoped MatrixGroups TensorProduct Polynomial
p2m_open "IsLocalRing CuspForm.TWLevel P2MW.S_CuspForm_TWLevel_HeckeRing_OperatorAlgebra_exists_U_eigenvector_H1_of_algHom.CuspForm.TWLevel"

namespace CuspForm
p2m_export "CuspForm" "mk smul_apply zero_apply ext neg_apply add_apply TWLevel.HeckeRing heckeAlgebra"
namespace TWLevel
p2m_export "CuspForm.TWLevel" "opML diaML_comm opML_mul_diaML heckeSubalgebra HeckeRing HeckeRing.act HeckeRing.act_injective HeckeRing.mem_heckeSubalgebra HeckeRing.T HeckeRing.act_T HeckeRing.diamond level HR Gen Carrier op OpComm thetaQ heckeData ML DiaComm diamondLin diaML Gen.T Gen.U"
namespace HeckeRing
p2m_export "CuspForm.TWLevel.HeckeRing" "instCommRing act act_injective mem_heckeSubalgebra ext T act_T diamond"
namespace OperatorAlgebra
namespace H1UPoint
p2m_open "CuspForm.TWLevel.HeckeRing CuspForm.TWLevel CuspForm"

section Group

open CongruenceSubgroup

theorem Gamma_le_GammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) : Gamma M ≤ CohCarrier.GammaH M H := by
  intro A hA
  rw [CohCarrier.mem_GammaH_iff]
  have hA' := Gamma_mem.mp hA
  have hA0 : A ∈ Gamma0 M := by rw [Gamma0_mem]; exact hA'.2.2.1
  refine ⟨hA0, ?_⟩
  have h1 : CohCarrier.gamma0Units M ⟨A, hA0⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    exact hA'.2.2.2
  rw [h1]
  exact one_mem H

theorem isCongruenceSubgroup_GammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    IsCongruenceSubgroup (CohCarrier.GammaH M H) :=
  ⟨M, NeZero.ne M, Gamma_le_GammaH M H⟩

scoped instance finiteIndex_GammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (CohCarrier.GammaH M H).FiniteIndex :=
  (isCongruenceSubgroup_GammaH M H).finiteIndex

scoped instance fg_SL2Z : Group.FG SL(2, ℤ) := by
  rw [Group.fg_iff]
  exact ⟨{ModularGroup.S, ModularGroup.T}, SpecialLinearGroup.SL2Z_generators,
    Set.toFinite _⟩

scoped instance fg_GammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) : Group.FG ↥(CohCarrier.GammaH M H) :=
  inferInstance

theorem exists_finset_closure_eq_top (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    ∃ s : Finset ↥(CohCarrier.GammaH M H), Subgroup.closure (s : Set ↥(CohCarrier.GammaH M H)) = ⊤ := by
  obtain ⟨s, hs⟩ := (Group.fg_def.mp (fg_GammaH M H))
  exact ⟨s, hs⟩

theorem H1_eq_of_eqOn {M : ℕ} {H : Subgroup (ZMod M)ˣ} {A : Type*} [AddCommGroup A]
    (s : Set ↥(CohCarrier.GammaH M H)) (hs : Subgroup.closure s = ⊤)
    (φ ψ : CohCarrier.H1 M H A) (h : ∀ g ∈ s, φ (Additive.ofMul g) = ψ (Additive.ofMul g)) :
    φ = ψ := by
  let K : Subgroup ↥(CohCarrier.GammaH M H) :=
    { carrier := {g | φ (Additive.ofMul g) = ψ (Additive.ofMul g)}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, ofMul_mul, map_add] at ha hb ⊢
        rw [ha, hb]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq, ofMul_inv, map_neg] at ha ⊢
        rw [ha] }
  have hK : (⊤ : Subgroup ↥(CohCarrier.GammaH M H)) ≤ K := by
    rw [← hs, Subgroup.closure_le]
    exact h
  ext g
  exact hK (Subgroup.mem_top (Additive.toMul g))

end Group

section Coeff

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ)

scoped instance isTorsionFree_H1 (𝒪 : Type) [CommRing 𝒪] : Module.IsTorsionFree 𝒪 (CohCarrier.H1 M H 𝒪) :=
  Function.Injective.moduleIsTorsionFree
    (fun φ : CohCarrier.H1 M H 𝒪 => (φ : Additive ↥(CohCarrier.GammaH M H) → 𝒪))
    DFunLike.coe_injective (fun _ _ => rfl)

variable {𝒪 : Type} [CommRing 𝒪] {F : Type} [Field F] [Algebra 𝒪 F]

noncomputable def coeffBil : F →ₗ[𝒪] CohCarrier.H1 M H 𝒪 →ₗ[𝒪] CohCarrier.H1 M H F :=
  LinearMap.mk₂ 𝒪
    (fun (c : F) (φ : CohCarrier.H1 M H 𝒪) =>
      (AddMonoidHom.mulLeft c).comp ((algebraMap 𝒪 F).toAddMonoidHom.comp φ))
    (fun c c' φ => AddMonoidHom.ext fun γ => by simp [add_mul])
    (fun a c φ => AddMonoidHom.ext fun γ => by simp [Algebra.smul_def, mul_assoc])
    (fun c φ ψ => AddMonoidHom.ext fun γ => by simp [mul_add])
    (fun a c φ => AddMonoidHom.ext fun γ => by
      show c * algebraMap 𝒪 F ((a • φ) γ) = a • (c * algebraMap 𝒪 F (φ γ))
      rw [AddMonoidHom.smul_apply, smul_eq_mul, map_mul, Algebra.smul_def]
      ring)

@[scoped simp] theorem coeffBil_apply (c : F) (φ : CohCarrier.H1 M H 𝒪) (γ : Additive ↥(CohCarrier.GammaH M H)) :
    coeffBil M H c φ γ = c * algebraMap 𝒪 F (φ γ) := rfl

noncomputable def coeffMapₒ : F ⊗[𝒪] CohCarrier.H1 M H 𝒪 →ₗ[𝒪] CohCarrier.H1 M H F :=
  TensorProduct.lift (coeffBil M H)

theorem coeffMapₒ_tmul (c : F) (φ : CohCarrier.H1 M H 𝒪) :
    coeffMapₒ M H (c ⊗ₜ φ) = coeffBil M H c φ :=
  TensorProduct.lift.tmul c φ

noncomputable def coeffMap : F ⊗[𝒪] CohCarrier.H1 M H 𝒪 →ₗ[F] CohCarrier.H1 M H F where
  toFun := coeffMapₒ M H
  map_add' x y := map_add _ x y
  map_smul' a x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c φ =>
      rw [TensorProduct.smul_tmul', coeffMapₒ_tmul, coeffMapₒ_tmul, RingHom.id_apply]
      refine AddMonoidHom.ext fun γ => ?_
      show (a • c) * algebraMap 𝒪 F (φ γ) = a • (c * algebraMap 𝒪 F (φ γ))
      rw [smul_eq_mul, smul_eq_mul, mul_assoc]
    | add x y hx hy =>
      simp only [smul_add, map_add, RingHom.id_apply] at hx hy ⊢
      rw [hx, hy]

theorem coeffMap_tmul (c : F) (φ : CohCarrier.H1 M H 𝒪) :
    coeffMap M H (c ⊗ₜ φ) = coeffBil M H c φ :=
  coeffMapₒ_tmul M H c φ

theorem coeffMap_heckeT (ℓ : ℕ) [NeZero ℓ] (x : F ⊗[𝒪] CohCarrier.H1 M H 𝒪) :
    coeffMap M H ((CohCarrier.heckeTL M H 𝒪 ℓ).baseChange F x) =
      CohCarrier.heckeT M H ℓ F (coeffMap M H x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c φ =>
    rw [LinearMap.baseChange_tmul, coeffMap_tmul, coeffMap_tmul, CohCarrier.heckeTL_apply]
    show (AddMonoidHom.mulLeft c).comp ((algebraMap 𝒪 F).toAddMonoidHom.comp
        (CohCarrier.heckeT M H ℓ 𝒪 φ)) = CohCarrier.heckeT M H ℓ F
        ((AddMonoidHom.mulLeft c).comp ((algebraMap 𝒪 F).toAddMonoidHom.comp φ))
    rw [← CohCarrier.heckeT_comp_coeff, ← CohCarrier.heckeT_comp_coeff]
  | add x y hx hy => rw [map_add, map_add, hx, hy, (coeffMap M H).map_add, map_add]

theorem coeffMap_diamondL [NeZero M] (u : (ZMod M)ˣ) (x : F ⊗[𝒪] CohCarrier.H1 M H 𝒪) :
    coeffMap M H ((CohCarrier.diamondL M H 𝒪 u).baseChange F x) =
      CohCarrier.diamondL M H F u (coeffMap M H x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c φ =>
    rw [LinearMap.baseChange_tmul, coeffMap_tmul, coeffMap_tmul]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, (coeffMap M H).map_add, map_add]

theorem coeffMap_injective [NeZero M] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    (hF : Function.Injective (algebraMap 𝒪 F)) : Function.Injective (coeffMap M H (𝒪 := 𝒪) (F := F)) := by
  classical
  haveI : IsNoetherianRing 𝒪 := inferInstance
  haveI : Module.Finite 𝒪 (CohCarrier.H1 M H 𝒪) := CohCarrier.H1_moduleFinite M H 𝒪 𝒪
  haveI : Module.Free 𝒪 (CohCarrier.H1 M H 𝒪) := inferInstance
  haveI : FaithfulSMul 𝒪 F := (faithfulSMul_iff_algebraMap_injective 𝒪 F).mpr hF
  obtain ⟨s, hs⟩ := exists_finset_closure_eq_top M H
  let b := Module.Free.chooseBasis 𝒪 (CohCarrier.H1 M H 𝒪)
  let bF := Algebra.TensorProduct.basis F b

  let v : Module.Free.ChooseBasisIndex 𝒪 (CohCarrier.H1 M H 𝒪) → (↥(s : Set ↥(CohCarrier.GammaH M H)) → 𝒪) :=
    fun i g => b i (Additive.ofMul (g : ↥(CohCarrier.GammaH M H)))
  have hv : LinearIndependent 𝒪 v := by
    rw [Fintype.linearIndependent_iff]
    intro y hy
    have hzero : ∑ i, y i • b i = 0 := by
      apply H1_eq_of_eqOn (s : Set ↥(CohCarrier.GammaH M H)) hs
      intro g hg
      have := congr_fun hy ⟨g, hg⟩
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, v] at this
      rw [AddMonoidHom.finsetSum_apply, AddMonoidHom.zero_apply]
      simpa [AddMonoidHom.smul_apply] using this
    exact (Fintype.linearIndependent_iff.mp b.linearIndependent) y hzero
  have hli := (linearIndependent_algebraMap_comp_iff (S := F)).mpr hv
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hxrepr : x = ∑ i, bF.repr x i • ((1 : F) ⊗ₜ b i) := by
    conv_lhs => rw [← bF.sum_repr x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply]
  have hcoef : ∑ i, bF.repr x i • (algebraMap 𝒪 F ∘ v i) = 0 := by
    ext ⟨g, hg⟩
    have h1 := congrArg (fun ψ : CohCarrier.H1 M H F => ψ (Additive.ofMul g)) hx
    simp only [AddMonoidHom.zero_apply] at h1
    rw [hxrepr, map_sum, AddMonoidHom.finsetSum_apply] at h1
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.zero_apply]
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, AddMonoidHom.smul_apply, coeffMap_tmul, coeffBil_apply, one_mul, smul_eq_mul]
  have hd : ∀ i, bF.repr x i = 0 := fun i =>
    (Fintype.linearIndependent_iff.mp hli) (fun i => bF.repr x i) hcoef i
  rw [hxrepr]
  simp [hd]

end Coeff

section Ext

theorem exists_ringHom_comp_eq_of_isIntegral {R S F : Type*} [CommRing R] [CommRing S]
    [Field F] [IsAlgClosed F] (i : R →+* S) (hi : i.IsIntegral) (hinj : Function.Injective i)
    (f : R →+* F) : ∃ g : S →+* F, g.comp i = f := by
  classical
  letI : Algebra R S := i.toAlgebra
  haveI : Algebra.IsIntegral R S := ⟨hi⟩
  have halg : ∀ x : R, algebraMap R S x = i x := fun x => rfl

  let P : Ideal R := RingHom.ker f
  haveI hP : P.IsPrime := RingHom.ker_isPrime f
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P (⊥ : Ideal S)
    (by
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_bot, halg] at hx
      have : x = 0 := hinj (by rw [map_zero]; exact hx)
      rw [this]; exact zero_mem P)
  haveI := hQ

  haveI hQc : (Q.comap (algebraMap R S)).IsPrime := Ideal.comap_isPrime _ Q
  haveI : IsDomain (S ⧸ Q) := Ideal.Quotient.isDomain Q
  haveI : IsDomain (R ⧸ Q.comap (algebraMap R S)) := Ideal.Quotient.isDomain _

  have hker : ∀ x ∈ Q.comap (algebraMap R S), f x = 0 := fun x hx => by
    rw [hQP] at hx; exact hx
  let f' : R ⧸ Q.comap (algebraMap R S) →+* F := Ideal.Quotient.lift _ f hker
  have hf'inj : Function.Injective f' :=
    RingHom.lift_injective_of_ker_le_ideal _ hker (by rw [hQP])
  letI : Algebra (R ⧸ Q.comap (algebraMap R S)) F := f'.toAlgebra
  haveI : Module.IsTorsionFree (R ⧸ Q.comap (algebraMap R S)) F :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hf'inj
  haveI : Module.IsTorsionFree (R ⧸ Q.comap (algebraMap R S)) (S ⧸ Q) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr Ideal.algebraMap_quotient_injective
  haveI : Algebra.IsIntegral (R ⧸ Q.comap (algebraMap R S)) (S ⧸ Q) := Algebra.IsIntegral.quotient
  haveI : Algebra.IsAlgebraic (R ⧸ Q.comap (algebraMap R S)) (S ⧸ Q) :=
    Algebra.IsIntegral.isAlgebraic
  let g' : (S ⧸ Q) →ₐ[R ⧸ Q.comap (algebraMap R S)] F := IsAlgClosed.lift
  refine ⟨g'.toRingHom.comp (Ideal.Quotient.mk Q), ?_⟩
  refine RingHom.ext fun x => ?_
  show g' (Ideal.Quotient.mk Q (i x)) = f x
  have h1 : Ideal.Quotient.mk Q (i x) =
      algebraMap (R ⧸ Q.comap (algebraMap R S)) (S ⧸ Q) (Ideal.Quotient.mk _ x) := rfl
  rw [h1, g'.commutes]
  show f' (Ideal.Quotient.mk _ x) = f x
  exact Ideal.Quotient.lift_mk _ f hker

theorem finite_end {𝒪 : Type*} [CommRing 𝒪] [IsNoetherianRing 𝒪] (M : Type*) [AddCommGroup M]
    [Module 𝒪 M] [Module.Finite 𝒪 M] : Module.Finite 𝒪 (Module.End 𝒪 M) := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' 𝒪 M
  have hinj : Function.Injective
      (LinearMap.lcomp 𝒪 M π : Module.End 𝒪 M →ₗ[𝒪] ((Fin n → 𝒪) →ₗ[𝒪] M)) := by
    intro f g hfg
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := hπ x
    exact congrArg (fun h : (Fin n → 𝒪) →ₗ[𝒪] M => h y) hfg
  exact Module.Finite.of_injective _ hinj

end Ext

noncomputable section Hecke

variable (N r : ℕ) {t : ℕ} (qv : Fin t → ℕ) (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
  (H : Subgroup (ZMod (level N r qv))ˣ) [NeZero N] [NeZero r] [∀ i, NeZero (qv i)]
  (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪)
  (α : Fin t → IsLocalRing.ResidueField 𝒪)
  (hc : OpComm N r qv S 𝒪 H) (hdc : DiaComm N r qv S 𝒪 H)

abbrev M0 : Type := Carrier N r qv 𝒪 H

abbrev E1 : Type := Module.End (heckeData N r qv S 𝒪 H θ α hc).FreeAlg (M0 N r qv 𝒪 H)

scoped instance : IsScalarTower 𝒪 (heckeData N r qv S 𝒪 H θ α hc).FreeAlg (M0 N r qv 𝒪 H) :=
  CohCarrier.HeckeData.V_isScalarTower _

noncomputable def genX (g : Gen (level N r qv) S t) : E1 N r qv S 𝒪 H θ α hc :=
  LinearMap.lsmul (heckeData N r qv S 𝒪 H θ α hc).FreeAlg (M0 N r qv 𝒪 H) (MvPolynomial.X g)

omit [NeZero r] in
theorem genX_apply (g : Gen (level N r qv) S t) (v : M0 N r qv 𝒪 H) :
    genX N r qv S 𝒪 H θ α hc g v = op N r qv S 𝒪 H g v := by
  show (heckeData N r qv S 𝒪 H θ α hc).opAlgHom (MvPolynomial.X g) v = _
  rw [CohCarrier.HeckeData.opAlgHom_X]
  rfl

def rawGens : Set (E1 N r qv S 𝒪 H θ α hc) :=
  {x | ∃ g : Gen (level N r qv) S t, x = genX N r qv S 𝒪 H θ α hc g} ∪
  {x | ∃ u ∈ HR N r qv, x = diamondLin N r qv S 𝒪 H θ α hc hdc u}

theorem genX_comm_diamondLin (g : Gen (level N r qv) S t) (u : (ZMod (level N r qv))ˣ) :
    genX N r qv S 𝒪 H θ α hc g * diamondLin N r qv S 𝒪 H θ α hc hdc u =
      diamondLin N r qv S 𝒪 H θ α hc hdc u * genX N r qv S 𝒪 H θ α hc g := by
  apply LinearMap.ext
  intro v
  show (MvPolynomial.X g : (heckeData N r qv S 𝒪 H θ α hc).FreeAlg) •
      diamondLin N r qv S 𝒪 H θ α hc hdc u v =
    diamondLin N r qv S 𝒪 H θ α hc hdc u ((MvPolynomial.X g : (heckeData N r qv S 𝒪 H θ α hc).FreeAlg) • v)
  rw [LinearMap.map_smul]

theorem diamondLin_comm (u v : (ZMod (level N r qv))ˣ) :
    diamondLin N r qv S 𝒪 H θ α hc hdc u * diamondLin N r qv S 𝒪 H θ α hc hdc v =
      diamondLin N r qv S 𝒪 H θ α hc hdc v * diamondLin N r qv S 𝒪 H θ α hc hdc u := by
  apply LinearMap.ext
  intro w
  show CohCarrier.diamondL _ H 𝒪 u (CohCarrier.diamondL _ H 𝒪 v w) =
    CohCarrier.diamondL _ H 𝒪 v (CohCarrier.diamondL _ H 𝒪 u w)
  rw [← Module.End.mul_apply, CohCarrier.diamondL_comm, Module.End.mul_apply]

theorem rawGens_comm : ∀ a ∈ rawGens N r qv S 𝒪 H θ α hc hdc, ∀ b ∈ rawGens N r qv S 𝒪 H θ α hc hdc,
    a * b = b * a := by
  rintro a (⟨g, rfl⟩ | ⟨u, hu, rfl⟩) b (⟨g', rfl⟩ | ⟨v, hv, rfl⟩)
  · apply LinearMap.ext
    intro v
    show (MvPolynomial.X _ : (heckeData N r qv S 𝒪 H θ α hc).FreeAlg) •
        ((MvPolynomial.X _ : (heckeData N r qv S 𝒪 H θ α hc).FreeAlg) • v) =
      (MvPolynomial.X _ : (heckeData N r qv S 𝒪 H θ α hc).FreeAlg) •
        ((MvPolynomial.X _ : (heckeData N r qv S 𝒪 H θ α hc).FreeAlg) • v)
    rw [← mul_smul, mul_comm, mul_smul]
  · exact genX_comm_diamondLin N r qv S 𝒪 H θ α hc hdc _ v
  · exact (genX_comm_diamondLin N r qv S 𝒪 H θ α hc hdc _ u).symm
  · exact diamondLin_comm N r qv S 𝒪 H θ α hc hdc u v

def T0 : Subalgebra 𝒪 (E1 N r qv S 𝒪 H θ α hc) := Algebra.adjoin 𝒪 (rawGens N r qv S 𝒪 H θ α hc hdc)

scoped instance T0.isMulCommutative : IsMulCommutative ↥(T0 N r qv S 𝒪 H θ α hc hdc) :=
  Algebra.isMulCommutative_adjoin 𝒪 (rawGens_comm N r qv S 𝒪 H θ α hc hdc)

p2m_reactivate "P2MW.S_CuspForm_TWLevel_HeckeRing_OperatorAlgebra_exists_U_eigenvector_H1_of_algHom.CuspForm.TWLevel.HeckeRing.OperatorAlgebra.H1UPoint.T0"
scoped instance T0.instCommRing : CommRing ↥(T0 N r qv S 𝒪 H θ α hc hdc) :=
  { (T0 N r qv S 𝒪 H θ α hc hdc).toRing with
    mul_comm := (T0.isMulCommutative N r qv S 𝒪 H θ α hc hdc).is_comm.comm }

p2m_reactivate "P2MW.S_CuspForm_TWLevel_HeckeRing_OperatorAlgebra_exists_U_eigenvector_H1_of_algHom.CuspForm.TWLevel.HeckeRing.OperatorAlgebra.H1UPoint.T0"

theorem T0_comm_diamondLin (x : ↥(T0 N r qv S 𝒪 H θ α hc hdc)) (u : (ZMod (level N r qv))ˣ) :
    (x : E1 N r qv S 𝒪 H θ α hc) * diamondLin N r qv S 𝒪 H θ α hc hdc u =
      diamondLin N r qv S 𝒪 H θ α hc hdc u * x := by
  have hle : T0 N r qv S 𝒪 H θ α hc hdc ≤
      Subalgebra.centralizer 𝒪 {y | ∃ v : (ZMod (level N r qv))ˣ,
        y = diamondLin N r qv S 𝒪 H θ α hc hdc v} := by
    refine Algebra.adjoin_le ?_
    rintro a (⟨g, rfl⟩ | ⟨w, hw, rfl⟩)
    · rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
      rintro _ ⟨v, rfl⟩
      exact (genX_comm_diamondLin N r qv S 𝒪 H θ α hc hdc _ v).symm
    · rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
      rintro _ ⟨v, rfl⟩
      exact diamondLin_comm N r qv S 𝒪 H θ α hc hdc v w
  exact ((Subalgebra.mem_centralizer_iff 𝒪).mp (hle x.2) _ ⟨u, rfl⟩).symm

def toEndO : E1 N r qv S 𝒪 H θ α hc →ₐ[𝒪] Module.End 𝒪 (M0 N r qv 𝒪 H) where
  toFun x := x.restrictScalars 𝒪
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' c := by
    apply LinearMap.ext
    intro v
    rfl

omit [NeZero r] in
theorem toEndO_injective : Function.Injective (toEndO N r qv S 𝒪 H θ α hc) :=
  fun _ _ h => LinearMap.restrictScalars_injective 𝒪 h

def act0 : ↥(T0 N r qv S 𝒪 H θ α hc hdc) →ₐ[𝒪] Module.End 𝒪 (M0 N r qv 𝒪 H) :=
  (toEndO N r qv S 𝒪 H θ α hc).comp (T0 N r qv S 𝒪 H θ α hc hdc).val

theorem act0_injective : Function.Injective (act0 N r qv S 𝒪 H θ α hc hdc) :=
  (toEndO_injective N r qv S 𝒪 H θ α hc).comp Subtype.val_injective

theorem act0_apply (x : ↥(T0 N r qv S 𝒪 H θ α hc hdc)) (v : M0 N r qv 𝒪 H) :
    act0 N r qv S 𝒪 H θ α hc hdc x v = (x : E1 N r qv S 𝒪 H θ α hc) v := rfl

noncomputable def locEnd : E1 N r qv S 𝒪 H θ α hc →ₐ[𝒪] Module.End 𝒪 (ML N r qv S 𝒪 H θ α hc) where
  toFun x := ((LocalizedModule.map (heckeData N r qv S 𝒪 H θ α hc).mTheta.primeCompl x).restrictScalars
      (heckeData N r qv S 𝒪 H θ α hc).FreeAlg).restrictScalars 𝒪
  map_one' := by
    apply LinearMap.ext
    intro y
    induction y using LocalizedModule.induction_on with
    | h m s =>
      show LocalizedModule.map _ (1 : E1 N r qv S 𝒪 H θ α hc) (LocalizedModule.mk m s) = LocalizedModule.mk m s
      rw [LocalizedModule.map_mk]
      rfl
  map_mul' x y := by
    apply LinearMap.ext
    intro z
    induction z using LocalizedModule.induction_on with
    | h m s =>
      show LocalizedModule.map _ (x * y) (LocalizedModule.mk m s) =
        LocalizedModule.map _ x (LocalizedModule.map _ y (LocalizedModule.mk m s))
      rw [LocalizedModule.map_mk, LocalizedModule.map_mk, LocalizedModule.map_mk]
      rfl
  map_zero' := by
    apply LinearMap.ext
    intro y
    induction y using LocalizedModule.induction_on with
    | h m s =>
      show LocalizedModule.map _ (0 : E1 N r qv S 𝒪 H θ α hc) (LocalizedModule.mk m s) = 0
      rw [LocalizedModule.map_mk, LinearMap.zero_apply, LocalizedModule.zero_mk]
  map_add' x y := by
    apply LinearMap.ext
    intro z
    show LocalizedModule.map _ (x + y) z = LocalizedModule.map _ x z + LocalizedModule.map _ y z
    rw [map_add, LinearMap.add_apply]
  commutes' c := by
    apply LinearMap.ext
    intro y
    induction y using LocalizedModule.induction_on with
    | h m s =>
      show LocalizedModule.map _ (algebraMap 𝒪 (E1 N r qv S 𝒪 H θ α hc) c) (LocalizedModule.mk m s) =
        c • LocalizedModule.mk m s
      rw [LocalizedModule.map_mk, Module.algebraMap_end_apply,
        ← IsScalarTower.algebraMap_smul (heckeData N r qv S 𝒪 H θ α hc).FreeAlg c m,
        ← LocalizedModule.smul'_mk, IsScalarTower.algebraMap_smul]

omit [NeZero r] in
theorem locEnd_genX (g : Gen (level N r qv) S t) :
    locEnd N r qv S 𝒪 H θ α hc (genX N r qv S 𝒪 H θ α hc g) =
      opML N r qv S 𝒪 H θ α hc (MvPolynomial.X g) := by
  apply LinearMap.ext
  intro y
  induction y using LocalizedModule.induction_on with
  | h m s =>
    show LocalizedModule.map _ (genX N r qv S 𝒪 H θ α hc g) (LocalizedModule.mk m s) =
      (MvPolynomial.X g : (heckeData N r qv S 𝒪 H θ α hc).FreeAlg) • LocalizedModule.mk m s
    rw [LocalizedModule.map_mk, LocalizedModule.smul'_mk]
    rfl

theorem locEnd_diamondLin (u : (ZMod (level N r qv))ˣ) :
    locEnd N r qv S 𝒪 H θ α hc (diamondLin N r qv S 𝒪 H θ α hc hdc u) =
      diaML N r qv S 𝒪 H θ α hc hdc u := rfl

def gensU : Set (Module.End 𝒪 (ML N r qv S 𝒪 H θ α hc)) :=
  {T | ∃ g : Gen (level N r qv) S t, T = opML N r qv S 𝒪 H θ α hc (MvPolynomial.X g)} ∪
  {D | ∃ u ∈ HR N r qv, D = diaML N r qv S 𝒪 H θ α hc hdc u}

theorem gensU_comm : ∀ a ∈ gensU N r qv S 𝒪 H θ α hc hdc, ∀ b ∈ gensU N r qv S 𝒪 H θ α hc hdc,
    a * b = b * a := by
  rintro a (⟨g, rfl⟩ | ⟨u, hu, rfl⟩) b (⟨g', rfl⟩ | ⟨v, hv, rfl⟩)
  · rw [← map_mul, ← map_mul, mul_comm]
  · exact opML_mul_diaML N r qv S 𝒪 H θ α hc hdc _ v
  · exact (opML_mul_diaML N r qv S 𝒪 H θ α hc hdc _ u).symm
  · exact diaML_comm N r qv S 𝒪 H θ α hc hdc u v

def BU : Subalgebra 𝒪 (Module.End 𝒪 (ML N r qv S 𝒪 H θ α hc)) :=
  Algebra.adjoin 𝒪 (gensU N r qv S 𝒪 H θ α hc hdc)

scoped instance BU.isMulCommutative : IsMulCommutative ↥(BU N r qv S 𝒪 H θ α hc hdc) :=
  Algebra.isMulCommutative_adjoin 𝒪 (gensU_comm N r qv S 𝒪 H θ α hc hdc)

p2m_reactivate "P2MW.S_CuspForm_TWLevel_HeckeRing_OperatorAlgebra_exists_U_eigenvector_H1_of_algHom.CuspForm.TWLevel.HeckeRing.OperatorAlgebra.H1UPoint.T0 P2MW.S_CuspForm_TWLevel_HeckeRing_OperatorAlgebra_exists_U_eigenvector_H1_of_algHom.CuspForm.TWLevel.HeckeRing.OperatorAlgebra.H1UPoint.BU"
scoped instance BU.instCommRing : CommRing ↥(BU N r qv S 𝒪 H θ α hc hdc) :=
  { (BU N r qv S 𝒪 H θ α hc hdc).toRing with
    mul_comm := (BU.isMulCommutative N r qv S 𝒪 H θ α hc hdc).is_comm.comm }

p2m_reactivate "P2MW.S_CuspForm_TWLevel_HeckeRing_OperatorAlgebra_exists_U_eigenvector_H1_of_algHom.CuspForm.TWLevel.HeckeRing.OperatorAlgebra.H1UPoint.T0 P2MW.S_CuspForm_TWLevel_HeckeRing_OperatorAlgebra_exists_U_eigenvector_H1_of_algHom.CuspForm.TWLevel.HeckeRing.OperatorAlgebra.H1UPoint.BU"
theorem heckeSubalgebra_le_BU :
    heckeSubalgebra N r qv S 𝒪 H θ α hc hdc ≤ BU N r qv S 𝒪 H θ α hc hdc := by
  refine Algebra.adjoin_le ?_
  rintro a (⟨ℓ, hℓ, hℓS, hℓL, rfl⟩ | ⟨u, hu, rfl⟩)
  · exact Algebra.subset_adjoin (Or.inl ⟨Gen.T ℓ hℓ hℓS hℓL, rfl⟩)
  · exact Algebra.subset_adjoin (Or.inr ⟨u, hu, rfl⟩)

theorem locEnd_mem_BU (x : ↥(T0 N r qv S 𝒪 H θ α hc hdc)) :
    locEnd N r qv S 𝒪 H θ α hc x ∈ BU N r qv S 𝒪 H θ α hc hdc := by
  have hle : (T0 N r qv S 𝒪 H θ α hc hdc).map (locEnd N r qv S 𝒪 H θ α hc) ≤
      BU N r qv S 𝒪 H θ α hc hdc := by
    rw [T0, AlgHom.map_adjoin]
    refine Algebra.adjoin_mono ?_
    rintro _ ⟨a, (⟨g, rfl⟩ | ⟨u, hu, rfl⟩), rfl⟩
    · exact Or.inl ⟨g, locEnd_genX N r qv S 𝒪 H θ α hc _⟩
    · exact Or.inr ⟨u, hu, locEnd_diamondLin N r qv S 𝒪 H θ α hc hdc u⟩
  exact hle (Subalgebra.mem_map.mpr ⟨x, x.2, rfl⟩)

def rB : ↥(T0 N r qv S 𝒪 H θ α hc hdc) →ₐ[𝒪] ↥(BU N r qv S 𝒪 H θ α hc hdc) :=
  ((locEnd N r qv S 𝒪 H θ α hc).comp (T0 N r qv S 𝒪 H θ α hc hdc).val).codRestrict
    (BU N r qv S 𝒪 H θ α hc hdc) (fun x => locEnd_mem_BU N r qv S 𝒪 H θ α hc hdc x)

theorem coe_rB (x : ↥(T0 N r qv S 𝒪 H θ α hc hdc)) :
    ((rB N r qv S 𝒪 H θ α hc hdc x : ↥(BU N r qv S 𝒪 H θ α hc hdc)) :
      Module.End 𝒪 (ML N r qv S 𝒪 H θ α hc)) = locEnd N r qv S 𝒪 H θ α hc x := rfl

def incl : HeckeRing N r qv S 𝒪 H θ α hc hdc →ₐ[𝒪] ↥(BU N r qv S 𝒪 H θ α hc hdc) :=
  (HeckeRing.act N r qv S 𝒪 H θ α hc hdc).codRestrict (BU N r qv S 𝒪 H θ α hc hdc)
    (fun x => heckeSubalgebra_le_BU N r qv S 𝒪 H θ α hc hdc
      (HeckeRing.mem_heckeSubalgebra N r qv S 𝒪 H θ α hc hdc x))

theorem coe_incl (x : HeckeRing N r qv S 𝒪 H θ α hc hdc) :
    ((incl N r qv S 𝒪 H θ α hc hdc x : ↥(BU N r qv S 𝒪 H θ α hc hdc)) :
      Module.End 𝒪 (ML N r qv S 𝒪 H θ α hc)) = HeckeRing.act N r qv S 𝒪 H θ α hc hdc x := rfl

theorem incl_injective : Function.Injective (incl N r qv S 𝒪 H θ α hc hdc) := by
  intro x y h
  have h1 := congrArg (fun z : ↥(BU N r qv S 𝒪 H θ α hc hdc) => (z : Module.End 𝒪 (ML N r qv S 𝒪 H θ α hc))) h
  exact HeckeRing.act_injective N r qv S 𝒪 H θ α hc hdc h1

def genG (g : Gen (level N r qv) S t) : ↥(T0 N r qv S 𝒪 H θ α hc hdc) :=
  ⟨genX N r qv S 𝒪 H θ α hc g, Algebra.subset_adjoin (Or.inl ⟨g, rfl⟩)⟩

def genDia (u : (ZMod (level N r qv))ˣ) (hu : u ∈ HR N r qv) : ↥(T0 N r qv S 𝒪 H θ α hc hdc) :=
  ⟨diamondLin N r qv S 𝒪 H θ α hc hdc u, Algebra.subset_adjoin (Or.inr ⟨u, hu, rfl⟩)⟩

theorem rB_genT (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ level N r qv) :
    rB N r qv S 𝒪 H θ α hc hdc (genG N r qv S 𝒪 H θ α hc hdc (Gen.T ℓ hℓ hℓS hℓL)) =
      incl N r qv S 𝒪 H θ α hc hdc (HeckeRing.T N r qv S 𝒪 H θ α hc hdc ℓ hℓ hℓS hℓL) :=
  Subtype.ext (by
    rw [coe_rB, coe_incl, HeckeRing.act_T]
    exact locEnd_genX N r qv S 𝒪 H θ α hc _)

theorem rB_genDia (u : (ZMod (level N r qv))ˣ) (hu : u ∈ HR N r qv) :
    rB N r qv S 𝒪 H θ α hc hdc (genDia N r qv S 𝒪 H θ α hc hdc u hu) =
      incl N r qv S 𝒪 H θ α hc hdc (HeckeRing.diamond N r qv S 𝒪 H θ α hc hdc u hu) :=
  Subtype.ext rfl

theorem coe_rB_genG (g : Gen (level N r qv) S t) :
    ((rB N r qv S 𝒪 H θ α hc hdc (genG N r qv S 𝒪 H θ α hc hdc g) : ↥(BU N r qv S 𝒪 H θ α hc hdc)) :
      Module.End 𝒪 (ML N r qv S 𝒪 H θ α hc)) = opML N r qv S 𝒪 H θ α hc (MvPolynomial.X g) := by
  rw [coe_rB]
  exact locEnd_genX N r qv S 𝒪 H θ α hc g

theorem act0_genG (g : Gen (level N r qv) S t) :
    act0 N r qv S 𝒪 H θ α hc hdc (genG N r qv S 𝒪 H θ α hc hdc g) = op N r qv S 𝒪 H g := by
  apply LinearMap.ext
  intro v
  rw [act0_apply]
  exact genX_apply N r qv S 𝒪 H θ α hc _ v

theorem act0_genDia (u : (ZMod (level N r qv))ˣ) (hu : u ∈ HR N r qv) :
    act0 N r qv S 𝒪 H θ α hc hdc (genDia N r qv S 𝒪 H θ α hc hdc u hu) =
      CohCarrier.diamondL (level N r qv) H 𝒪 u := by
  apply LinearMap.ext
  intro v
  rfl

def dia : (ZMod (level N r qv))ˣ →* Module.End 𝒪 (M0 N r qv 𝒪 H) where
  toFun u := CohCarrier.diamondL (level N r qv) H 𝒪 u
  map_one' := CohCarrier.diamondL_one _ H 𝒪
  map_mul' u v := CohCarrier.diamondL_mul _ H 𝒪 u v

omit [IsLocalRing 𝒪] in
theorem dia_apply (u : (ZMod (level N r qv))ˣ) : dia N r qv 𝒪 H u = CohCarrier.diamondL (level N r qv) H 𝒪 u :=
  rfl

theorem dia_comm_act0 (u : (ZMod (level N r qv))ˣ) (x : ↥(T0 N r qv S 𝒪 H θ α hc hdc)) :
    dia N r qv 𝒪 H u * act0 N r qv S 𝒪 H θ α hc hdc x = act0 N r qv S 𝒪 H θ α hc hdc x * dia N r qv 𝒪 H u := by
  apply LinearMap.ext
  intro v
  have := LinearMap.congr_fun (T0_comm_diamondLin N r qv S 𝒪 H θ α hc hdc x u) v
  exact this.symm

theorem coe_aeval_BU (x : ↥(BU N r qv S 𝒪 H θ α hc hdc)) (q : 𝒪[X]) :
    ((Polynomial.aeval x q : ↥(BU N r qv S 𝒪 H θ α hc hdc)) : Module.End 𝒪 (ML N r qv S 𝒪 H θ α hc)) =
      Polynomial.aeval ((x : ↥(BU N r qv S 𝒪 H θ α hc hdc)) : Module.End 𝒪 (ML N r qv S 𝒪 H θ α hc)) q :=
  (Polynomial.aeval_algHom_apply (BU N r qv S 𝒪 H θ α hc hdc).val x q).symm

theorem coe_zero_BU :
    ((0 : ↥(BU N r qv S 𝒪 H θ α hc hdc)) : Module.End 𝒪 (ML N r qv S 𝒪 H θ α hc)) = 0 := rfl

omit [NeZero r] in
theorem aeval_opML_X_sub_C (g : Gen (level N r qv) S t) (a : 𝒪) :
    Polynomial.aeval (opML N r qv S 𝒪 H θ α hc (MvPolynomial.X g)) (Polynomial.X - Polynomial.C a) =
      opML N r qv S 𝒪 H θ α hc
        ((MvPolynomial.X g : (heckeData N r qv S 𝒪 H θ α hc).FreeAlg) - MvPolynomial.C a) := by
  rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, map_sub]
  congr 1
  rw [show (MvPolynomial.C a : (heckeData N r qv S 𝒪 H θ α hc).FreeAlg) =
    algebraMap 𝒪 (heckeData N r qv S 𝒪 H θ α hc).FreeAlg a from rfl, AlgHom.commutes]

omit [NeZero r] in

theorem thetaTilde_X_sub_C (g : Gen (level N r qv) S t) (a : 𝒪)
    (ha : residue 𝒪 a = thetaQ N r qv S (ResidueField 𝒪) θ α g) :
    (heckeData N r qv S 𝒪 H θ α hc).thetaTilde
      ((MvPolynomial.X g : (heckeData N r qv S 𝒪 H θ α hc).FreeAlg) - MvPolynomial.C a) = 0 := by
  have h1 : (heckeData N r qv S 𝒪 H θ α hc).thetaTilde (MvPolynomial.X g) =
      thetaQ N r qv S (ResidueField 𝒪) θ α g := by
    show MvPolynomial.aeval (heckeData N r qv S 𝒪 H θ α hc).θbar
      (MvPolynomial.X g : (heckeData N r qv S 𝒪 H θ α hc).FreeAlg) = _
    rw [MvPolynomial.aeval_X]
    rfl
  have h2 : (heckeData N r qv S 𝒪 H θ α hc).thetaTilde (MvPolynomial.C a) = residue 𝒪 a := by
    show MvPolynomial.aeval (heckeData N r qv S 𝒪 H θ α hc).θbar
      (MvPolynomial.C a : (heckeData N r qv S 𝒪 H θ α hc).FreeAlg) = _
    rw [MvPolynomial.algHom_C, IsLocalRing.ResidueField.algebraMap_eq]
  rw [map_sub, h1, h2, ha, sub_self]

theorem aeval_rB_genG_comp_eq_zero (g : Gen (level N r qv) S t) (a : 𝒪) (P : 𝒪[X])
    (hP : Polynomial.aeval (opML N r qv S 𝒪 H θ α hc
      ((MvPolynomial.X g : (heckeData N r qv S 𝒪 H θ α hc).FreeAlg) - MvPolynomial.C a)) P = 0) :
    Polynomial.aeval (rB N r qv S 𝒪 H θ α hc hdc (genG N r qv S 𝒪 H θ α hc hdc g))
      (P.comp (Polynomial.X - Polynomial.C a)) = 0 := by
  apply Subtype.ext
  rw [coe_aeval_BU, coe_zero_BU, coe_rB_genG, Polynomial.aeval_comp, aeval_opML_X_sub_C, hP]

omit [NeZero N] [NeZero r] [∀ i, NeZero (qv i)] [IsLocalRing 𝒪] in

theorem aeval_sub_algebraMap {A : Type*} [CommRing A] [Algebra 𝒪 A] (x : A) (a : 𝒪) (P : 𝒪[X]) :
    Polynomial.aeval (x - algebraMap 𝒪 A a) P = Polynomial.aeval x (P.comp (Polynomial.X - Polynomial.C a)) := by
  rw [Polynomial.aeval_comp, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]

theorem aeval_apply_rB_sub_eq_zero {F : Type*} [CommRing F] [Algebra 𝒪 F]
    (Λ : ↥(BU N r qv S 𝒪 H θ α hc hdc) →ₐ[𝒪] F) (g : Gen (level N r qv) S t) (a : 𝒪) (P : 𝒪[X])
    (hP : Polynomial.aeval (opML N r qv S 𝒪 H θ α hc
      ((MvPolynomial.X g : (heckeData N r qv S 𝒪 H θ α hc).FreeAlg) - MvPolynomial.C a)) P = 0) :
    Polynomial.aeval (Λ (rB N r qv S 𝒪 H θ α hc hdc (genG N r qv S 𝒪 H θ α hc hdc g)) - algebraMap 𝒪 F a) P
      = 0 := by
  rw [aeval_sub_algebraMap, Polynomial.aeval_algHom_apply,
    aeval_rB_genG_comp_eq_zero N r qv S 𝒪 H θ α hc hdc g a P hP, map_zero]

theorem exists_algHom_BU_extend [IsNoetherianRing 𝒪] [Module.Finite 𝒪 (ML N r qv S 𝒪 H θ α hc)]
    (F : Type) [Field F] [IsAlgClosed F] [Algebra 𝒪 F]
    (lam : HeckeRing N r qv S 𝒪 H θ α hc hdc →ₐ[𝒪] F) :
    ∃ Λ : ↥(BU N r qv S 𝒪 H θ α hc hdc) →ₐ[𝒪] F, ∀ x, Λ (incl N r qv S 𝒪 H θ α hc hdc x) = lam x := by
  haveI : Module.Finite 𝒪 (Module.End 𝒪 (ML N r qv S 𝒪 H θ α hc)) := finite_end (ML N r qv S 𝒪 H θ α hc)
  haveI : Module.Finite 𝒪 ↥(BU N r qv S 𝒪 H θ α hc hdc) :=
    Module.Finite.of_injective (BU N r qv S 𝒪 H θ α hc hdc).val.toLinearMap Subtype.val_injective
  haveI : Algebra.IsIntegral 𝒪 ↥(BU N r qv S 𝒪 H θ α hc hdc) := Algebra.IsIntegral.of_finite 𝒪 _
  have hi : (incl N r qv S 𝒪 H θ α hc hdc).toRingHom.IsIntegral := by
    intro b
    obtain ⟨p, hpm, hp0⟩ := (Algebra.IsIntegral.isIntegral (R := 𝒪) b)
    refine ⟨p.map (algebraMap 𝒪 (HeckeRing N r qv S 𝒪 H θ α hc hdc)), hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (incl N r qv S 𝒪 H θ α hc hdc).toRingHom.comp
        (algebraMap 𝒪 (HeckeRing N r qv S 𝒪 H θ α hc hdc)) = algebraMap 𝒪 ↥(BU N r qv S 𝒪 H θ α hc hdc) :=
      RingHom.ext fun x => (incl N r qv S 𝒪 H θ α hc hdc).commutes x
    rw [hcomp]
    exact hp0
  obtain ⟨g, hg⟩ := exists_ringHom_comp_eq_of_isIntegral (incl N r qv S 𝒪 H θ α hc hdc).toRingHom hi
    (incl_injective N r qv S 𝒪 H θ α hc hdc) lam.toRingHom
  have hg' : ∀ x, g (incl N r qv S 𝒪 H θ α hc hdc x) = lam x := fun x => RingHom.congr_fun hg x
  refine ⟨{ toRingHom := g
            commutes' := fun x => ?_ }, hg'⟩
  show g (algebraMap 𝒪 _ x) = algebraMap 𝒪 F x
  rw [← (incl N r qv S 𝒪 H θ α hc hdc).commutes x, hg', lam.commutes]

theorem repr_mem_of_mem_smul_top {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]
    {ι : Type*} (b : Module.Basis ι R V) (I : Ideal R) {x : V}
    (hx : x ∈ I • (⊤ : Submodule R V)) : ∀ i : ι, b.repr x i ∈ I := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro c hc y _ i
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact I.mul_mem_right _ hc
  · intro y z hy hz i
    rw [map_add, Finsupp.add_apply]
    exact I.add_mem (hy i) (hz i)

omit [NeZero r] in

theorem isUnit_opML_of_not_mem (s : (heckeData N r qv S 𝒪 H θ α hc).FreeAlg)
    (hs : s ∉ (heckeData N r qv S 𝒪 H θ α hc).mTheta) :
    IsUnit (opML N r qv S 𝒪 H θ α hc s) := by
  have hs' : s ∈ (heckeData N r qv S 𝒪 H θ α hc).mTheta.primeCompl := hs
  have hu := IsLocalizedModule.map_units
    (LocalizedModule.mkLinearMap (heckeData N r qv S 𝒪 H θ α hc).mTheta.primeCompl (M0 N r qv 𝒪 H))
    ⟨s, hs'⟩
  rw [Module.End.isUnit_iff] at hu ⊢
  exact hu

omit [NeZero r] in

theorem exists_monic_aeval_opML_eq_zero [IsNoetherianRing 𝒪]
    [Module.Finite 𝒪 (ML N r qv S 𝒪 H θ α hc)] [Module.Free 𝒪 (ML N r qv S 𝒪 H θ α hc)]
    (y : (heckeData N r qv S 𝒪 H θ α hc).FreeAlg)
    (hy : (heckeData N r qv S 𝒪 H θ α hc).thetaTilde y = 0) :
    ∃ P : 𝒪[X], P.Monic ∧ (∀ i < P.natDegree, P.coeff i ∈ maximalIdeal 𝒪) ∧
      Polynomial.aeval (opML N r qv S 𝒪 H θ α hc y) P = 0 := by
  classical

  have hGeq : ∀ q : 𝒪[X], Polynomial.aeval (opML N r qv S 𝒪 H θ α hc y) q =
      opML N r qv S 𝒪 H θ α hc (Polynomial.aeval y q) :=
    fun q => Polynomial.aeval_algHom_apply (opML N r qv S 𝒪 H θ α hc) y q
  have hθq : ∀ q : 𝒪[X], (heckeData N r qv S 𝒪 H θ α hc).thetaTilde (Polynomial.aeval y q) =
      residue 𝒪 (q.coeff 0) := by
    intro q
    rw [← Polynomial.aeval_algHom_apply, hy, Polynomial.aeval_def, Polynomial.eval₂_at_zero,
      IsLocalRing.ResidueField.algebraMap_eq]
  generalize hφ : opML N r qv S 𝒪 H θ α hc y = φ
  rw [hφ] at hGeq

  have hpφ : Polynomial.aeval φ φ.charpoly = 0 := LinearMap.aeval_self_charpoly φ
  have hpbar0 : φ.charpoly.map (residue 𝒪) ≠ 0 := (φ.charpoly_monic.map (residue 𝒪)).ne_zero
  obtain ⟨gbar, hfac, hndvd⟩ :=
    (φ.charpoly.map (residue 𝒪)).exists_eq_pow_rootMultiplicity_mul_and_not_dvd hpbar0 0
  rw [map_zero, sub_zero] at hfac hndvd
  generalize hm : (φ.charpoly.map (residue 𝒪)).rootMultiplicity 0 = m at hfac
  have hg0 : gbar.coeff 0 ≠ 0 := fun h => hndvd (Polynomial.X_dvd_iff.mpr h)

  obtain ⟨ghat, hghat⟩ := Polynomial.map_surjective (residue 𝒪) IsLocalRing.residue_surjective gbar
  have hhcoeff : ∀ i, (φ.charpoly - Polynomial.X ^ m * ghat).coeff i ∈ maximalIdeal 𝒪 := by
    intro i
    rw [← IsLocalRing.residue_eq_zero_iff, ← Polynomial.coeff_map, Polynomial.map_sub,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, hghat, ← hfac, sub_self,
      Polynomial.coeff_zero]

  have hsnot : Polynomial.aeval y ghat ∉ (heckeData N r qv S 𝒪 H θ α hc).mTheta := by
    intro hmem
    have h1 : (heckeData N r qv S 𝒪 H θ α hc).thetaTilde (Polynomial.aeval y ghat) = 0 := hmem
    rw [hθq] at h1
    apply hg0
    rw [← hghat, Polynomial.coeff_map, h1]
  have hGu : IsUnit (Polynomial.aeval φ ghat) := by
    rw [hGeq]
    exact isUnit_opML_of_not_mem N r qv S 𝒪 H θ α hc _ hsnot

  have hsum : φ ^ m * Polynomial.aeval φ ghat +
      Polynomial.aeval φ (φ.charpoly - Polynomial.X ^ m * ghat) = 0 := by
    rw [map_sub, map_mul, map_pow, Polynomial.aeval_X, hpφ, zero_sub, add_neg_cancel]
  have hφm : φ ^ m = (-Polynomial.aeval φ (φ.charpoly - Polynomial.X ^ m * ghat)) * ↑(hGu.unit⁻¹) := by
    have h1 : φ ^ m * Polynomial.aeval φ ghat =
        -Polynomial.aeval φ (φ.charpoly - Polynomial.X ^ m * ghat) := eq_neg_of_add_eq_zero_left hsum
    calc φ ^ m = φ ^ m * (Polynomial.aeval φ ghat * ↑(hGu.unit⁻¹)) := by
            rw [IsUnit.mul_val_inv, mul_one]
      _ = (φ ^ m * Polynomial.aeval φ ghat) * ↑(hGu.unit⁻¹) := by rw [mul_assoc]
      _ = (-Polynomial.aeval φ (φ.charpoly - Polynomial.X ^ m * ghat)) * ↑(hGu.unit⁻¹) := by
            rw [h1]
  have haeval_mem : ∀ z : ML N r qv S 𝒪 H θ α hc,
      Polynomial.aeval φ (φ.charpoly - Polynomial.X ^ m * ghat) z ∈
        (maximalIdeal 𝒪) • (⊤ : Submodule 𝒪 (ML N r qv S 𝒪 H θ α hc)) := by
    intro z
    rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [LinearMap.smul_apply]
    exact Submodule.smul_mem_smul (hhcoeff i) Submodule.mem_top
  have hnil : ∀ x : ML N r qv S 𝒪 H θ α hc,
      (φ ^ m) x ∈ (maximalIdeal 𝒪) • (⊤ : Submodule 𝒪 (ML N r qv S 𝒪 H θ α hc)) := by
    intro x
    rw [hφm, Module.End.mul_apply, LinearMap.neg_apply]
    exact Submodule.neg_mem _ (haeval_mem _)
  have hn0 : 0 < m + 1 := Nat.succ_pos m
  have hnil' : ∀ x : ML N r qv S 𝒪 H θ α hc,
      (φ ^ (m + 1)) x ∈ (maximalIdeal 𝒪) • (⊤ : Submodule 𝒪 (ML N r qv S 𝒪 H θ α hc)) := by
    intro x
    rw [pow_succ, Module.End.mul_apply]
    exact hnil (φ x)

  let b := Module.Free.chooseBasis 𝒪 (ML N r qv S 𝒪 H θ α hc)
  have hAmem : ∀ i j, LinearMap.toMatrix b b (φ ^ (m + 1)) i j ∈ maximalIdeal 𝒪 := by
    intro i j
    rw [LinearMap.toMatrix_apply]
    exact repr_mem_of_mem_smul_top b (maximalIdeal 𝒪) (hnil' (b j)) i
  have hP₀eq : (LinearMap.toMatrix b b (φ ^ (m + 1))).charpoly = (φ ^ (m + 1)).charpoly :=
    LinearMap.charpoly_toMatrix (φ ^ (m + 1)) b
  have hP₀monic : (LinearMap.toMatrix b b (φ ^ (m + 1))).charpoly.Monic := Matrix.charpoly_monic _
  have hP₀deg : (LinearMap.toMatrix b b (φ ^ (m + 1))).charpoly.natDegree =
      Fintype.card (Module.Free.ChooseBasisIndex 𝒪 (ML N r qv S 𝒪 H θ α hc)) :=
    Matrix.charpoly_natDegree_eq_dim _
  have hP₀coeff : ∀ i < (LinearMap.toMatrix b b (φ ^ (m + 1))).charpoly.natDegree,
      (LinearMap.toMatrix b b (φ ^ (m + 1))).charpoly.coeff i ∈ maximalIdeal 𝒪 := by
    intro i hi
    have h1 := Matrix.coeff_charpoly_mem_ideal_pow hAmem i
    rw [hP₀deg] at hi
    exact Ideal.pow_le_self (Nat.sub_ne_zero_of_lt hi) h1
  have hP₀aeval : Polynomial.aeval (φ ^ (m + 1)) (LinearMap.toMatrix b b (φ ^ (m + 1))).charpoly = 0 := by
    rw [hP₀eq]
    exact LinearMap.aeval_self_charpoly _

  refine ⟨Polynomial.expand 𝒪 (m + 1) (LinearMap.toMatrix b b (φ ^ (m + 1))).charpoly,
    hP₀monic.expand hn0, ?_, ?_⟩
  · intro i hi
    rw [Polynomial.coeff_expand hn0]
    split_ifs with hdvd
    · apply hP₀coeff
      rw [Polynomial.natDegree_expand] at hi
      exact Nat.div_lt_of_lt_mul (by rwa [mul_comm] at hi)
    · exact Ideal.zero_mem _
  · rw [Polynomial.expand_aeval, hP₀aeval]

end Hecke
p2m_reactivate "P2MW.S_CuspForm_TWLevel_HeckeRing_OperatorAlgebra_exists_U_eigenvector_H1_of_algHom.CuspForm.TWLevel.HeckeRing.OperatorAlgebra.H1UPoint.T0 P2MW.S_CuspForm_TWLevel_HeckeRing_OperatorAlgebra_exists_U_eigenvector_H1_of_algHom.CuspForm.TWLevel.HeckeRing.OperatorAlgebra.H1UPoint.BU"

section Main

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (maximalIdeal 𝒪) 𝒪]

theorem main
    (S : Set ℕ) (N : ℕ) [NeZero N] (r : ℕ) [NeZero r]
    (θ : CuspForm.heckeAlgebra N 2 S →+* ResidueField 𝒪)
    (t : ℕ) (qv : Fin t → ℕ) [∀ i, NeZero (qv i)] (α : Fin t → ResidueField 𝒪)
    (H : Subgroup (ZMod (level N r qv))ˣ)
    (hc : OpComm N r qv S 𝒪 H) (hdc : DiaComm N r qv S 𝒪 H)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra 𝒪 F]
    (hF : Function.Injective (algebraMap 𝒪 F))
    (lam : HeckeRing N r qv S 𝒪 H θ α hc hdc →ₐ[𝒪] F) :
    ∃ (e : (ZMod (level N r qv))ˣ →* Fˣ) (μ : Fin t → F) (c : CohCarrier.H1 (level N r qv) H F),
      c ≠ 0 ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ level N r qv),
        (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeT (level N r qv) H ℓ F c) =
          lam (HeckeRing.T N r qv S 𝒪 H θ α hc hdc ℓ hℓ hℓS hℓL) • c) ∧
      (∀ j : Fin t, CohCarrier.heckeT (level N r qv) H (qv j) F c = μ j • c) ∧
      (∀ u : (ZMod (level N r qv))ˣ,
        CohCarrier.diamondL (level N r qv) H F u c = ((e u : Fˣ) : F) • c) ∧
      (∀ (u : (ZMod (level N r qv))ˣ) (hu : u ∈ HR N r qv),
        ((e u : Fˣ) : F) = lam (HeckeRing.diamond N r qv S 𝒪 H θ α hc hdc u hu)) ∧
      (∀ u : (ZMod (level N r qv))ˣ, u ∈ H → e u = 1) ∧
      (∀ (j : Fin t) (a : 𝒪), IsLocalRing.residue 𝒪 a = α j →
        ∃ P : Polynomial 𝒪, P.Monic ∧ (∀ i < P.natDegree, P.coeff i ∈ maximalIdeal 𝒪) ∧
          Polynomial.aeval (μ j - algebraMap 𝒪 F a) P = 0) := by
  classical
  haveI : IsNoetherianRing 𝒪 := inferInstance
  haveI : Module.Finite 𝒪 (M0 N r qv 𝒪 H) := CohCarrier.H1_moduleFinite (level N r qv) H 𝒪 𝒪
  haveI : Module.Free 𝒪 (M0 N r qv 𝒪 H) := inferInstance

  obtain ⟨hMLfin, hMLfree⟩ := CohCarrier.HeckeData.finite_ML_and_free_ML (k := ResidueField 𝒪)
    IsLocalRing.residue_surjective (heckeData N r qv S 𝒪 H θ α hc)
  haveI : Module.Finite 𝒪 (ML N r qv S 𝒪 H θ α hc) := hMLfin
  haveI : Module.Free 𝒪 (ML N r qv S 𝒪 H θ α hc) := hMLfree inferInstance

  obtain ⟨Λ, hΛ⟩ := exists_algHom_BU_extend N r qv S 𝒪 H θ α hc hdc F lam

  let lam0 : ↥(T0 N r qv S 𝒪 H θ α hc hdc) →ₐ[𝒪] F := Λ.comp (rB N r qv S 𝒪 H θ α hc hdc)
  obtain ⟨e, w, hw0, hT, hD⟩ :=
    DeligneSerre.OperatorAlgebra.exists_eigenvector_baseChange_of_algHom
      (act0 N r qv S 𝒪 H θ α hc hdc) (act0_injective N r qv S 𝒪 H θ α hc hdc)
      (dia N r qv 𝒪 H) (dia_comm_act0 N r qv S 𝒪 H θ α hc hdc) hF lam0
  let U := coeffMap (level N r qv) H (𝒪 := 𝒪) (F := F)
  have hUinj : Function.Injective U := coeffMap_injective (level N r qv) H hF

  have hgen : ∀ (g₀ : Gen (level N r qv) S t) (ℓ : ℕ) [NeZero ℓ]
      (hop : op N r qv S 𝒪 H g₀ = CohCarrier.heckeTL (level N r qv) H 𝒪 ℓ),
      CohCarrier.heckeT (level N r qv) H ℓ F (U w) = lam0 (genG N r qv S 𝒪 H θ α hc hdc g₀) • U w := by
    intro g₀ ℓ _ hop
    have h1 := hT (genG N r qv S 𝒪 H θ α hc hdc g₀)
    rw [act0_genG, hop] at h1
    have h2 := congrArg U h1
    rw [map_smul, coeffMap_heckeT] at h2
    exact h2
  refine ⟨e, fun j => lam0 (genG N r qv S 𝒪 H θ α hc hdc (Gen.U j)), U w, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hw0 (hUinj (by rw [h, map_zero]))
  · intro ℓ hℓ hℓS hℓL
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    rw [hgen (Gen.T ℓ hℓ hℓS hℓL) ℓ rfl]
    congr 1
    show Λ (rB N r qv S 𝒪 H θ α hc hdc (genG N r qv S 𝒪 H θ α hc hdc (Gen.T ℓ hℓ hℓS hℓL))) = _
    rw [rB_genT, hΛ]
  · intro j
    exact hgen (Gen.U j) (qv j) rfl
  · intro u
    have h1 := congrArg U (hD u)
    rw [map_smul, dia_apply, coeffMap_diamondL] at h1
    exact h1
  · intro u hu
    have h1 := hT (genDia N r qv S 𝒪 H θ α hc hdc u hu)
    rw [act0_genDia] at h1
    have h2 := hD u
    rw [dia_apply, h1] at h2
    have h3 : lam0 (genDia N r qv S 𝒪 H θ α hc hdc u hu) = ((e u : Fˣ) : F) := smul_left_injective F hw0 h2
    rw [← h3]
    show Λ (rB N r qv S 𝒪 H θ α hc hdc (genDia N r qv S 𝒪 H θ α hc hdc u hu)) = _
    rw [rB_genDia, hΛ]
  · intro u hu
    have h2 := hD u
    rw [dia_apply, CohCarrier.diamondL_of_mem _ H 𝒪 u hu, LinearMap.baseChange_one,
      Module.End.one_apply] at h2
    have h3 : ((e u : Fˣ) : F) = 1 :=
      (smul_left_injective F hw0 (show (1 : F) • w = ((e u : Fˣ) : F) • w by
        rw [one_smul]; exact h2)).symm
    exact Units.val_eq_one.mp h3
  · intro j a ha

    obtain ⟨P, hPm, hPc, hPφ⟩ := exists_monic_aeval_opML_eq_zero N r qv S 𝒪 H θ α hc _
      (thetaTilde_X_sub_C N r qv S 𝒪 H θ α hc (Gen.U j) a ha)
    exact ⟨P, hPm, hPc, aeval_apply_rB_sub_eq_zero N r qv S 𝒪 H θ α hc hdc Λ (Gen.U j) a P hPφ⟩

end Main
p2m_reactivate "P2MW.S_CuspForm_TWLevel_HeckeRing_OperatorAlgebra_exists_U_eigenvector_H1_of_algHom.CuspForm.TWLevel.HeckeRing.OperatorAlgebra.H1UPoint.T0 P2MW.S_CuspForm_TWLevel_HeckeRing_OperatorAlgebra_exists_U_eigenvector_H1_of_algHom.CuspForm.TWLevel.HeckeRing.OperatorAlgebra.H1UPoint.BU"

end CuspForm.TWLevel.HeckeRing.OperatorAlgebra.H1UPoint
p2m_reactivate "P2MW.S_CuspForm_TWLevel_HeckeRing_OperatorAlgebra_exists_U_eigenvector_H1_of_algHom.CuspForm.TWLevel.HeckeRing.OperatorAlgebra.H1UPoint.T0 P2MW.S_CuspForm_TWLevel_HeckeRing_OperatorAlgebra_exists_U_eigenvector_H1_of_algHom.CuspForm.TWLevel.HeckeRing.OperatorAlgebra.H1UPoint.BU P2MW.S_CuspForm_TWLevel_HeckeRing_OperatorAlgebra_exists_U_eigenvector_H1_of_algHom.CuspForm P2MW.S_CuspForm_TWLevel_HeckeRing_OperatorAlgebra_exists_U_eigenvector_H1_of_algHom.CuspForm.TWLevel P2MW.S_CuspForm_TWLevel_HeckeRing_OperatorAlgebra_exists_U_eigenvector_H1_of_algHom.CuspForm.TWLevel.HeckeRing P2MW.S_CuspForm_TWLevel_HeckeRing_OperatorAlgebra_exists_U_eigenvector_H1_of_algHom.CuspForm.TWLevel.HeckeRing.OperatorAlgebra P2MW.S_CuspForm_TWLevel_HeckeRing_OperatorAlgebra_exists_U_eigenvector_H1_of_algHom.CuspForm.TWLevel.HeckeRing.OperatorAlgebra.H1UPoint"
p2m_reactivate "P2MW.S_CuspForm_TWLevel_HeckeRing_OperatorAlgebra_exists_U_eigenvector_H1_of_algHom.CuspForm.TWLevel.HeckeRing.OperatorAlgebra.H1UPoint.T0 P2MW.S_CuspForm_TWLevel_HeckeRing_OperatorAlgebra_exists_U_eigenvector_H1_of_algHom.CuspForm.TWLevel.HeckeRing.OperatorAlgebra.H1UPoint.BU P2MW.S_CuspForm_TWLevel_HeckeRing_OperatorAlgebra_exists_U_eigenvector_H1_of_algHom.CuspForm P2MW.S_CuspForm_TWLevel_HeckeRing_OperatorAlgebra_exists_U_eigenvector_H1_of_algHom.CuspForm.TWLevel P2MW.S_CuspForm_TWLevel_HeckeRing_OperatorAlgebra_exists_U_eigenvector_H1_of_algHom.CuspForm.TWLevel.HeckeRing P2MW.S_CuspForm_TWLevel_HeckeRing_OperatorAlgebra_exists_U_eigenvector_H1_of_algHom.CuspForm.TWLevel.HeckeRing.OperatorAlgebra"
p2m_reactivate "P2MW.S_CuspForm_TWLevel_HeckeRing_OperatorAlgebra_exists_U_eigenvector_H1_of_algHom.CuspForm.TWLevel.HeckeRing.OperatorAlgebra.H1UPoint.T0 P2MW.S_CuspForm_TWLevel_HeckeRing_OperatorAlgebra_exists_U_eigenvector_H1_of_algHom.CuspForm.TWLevel.HeckeRing.OperatorAlgebra.H1UPoint.BU P2MW.S_CuspForm_TWLevel_HeckeRing_OperatorAlgebra_exists_U_eigenvector_H1_of_algHom.CuspForm P2MW.S_CuspForm_TWLevel_HeckeRing_OperatorAlgebra_exists_U_eigenvector_H1_of_algHom.CuspForm.TWLevel P2MW.S_CuspForm_TWLevel_HeckeRing_OperatorAlgebra_exists_U_eigenvector_H1_of_algHom.CuspForm.TWLevel.HeckeRing"
p2m_reactivate "P2MW.S_CuspForm_TWLevel_HeckeRing_OperatorAlgebra_exists_U_eigenvector_H1_of_algHom.CuspForm.TWLevel.HeckeRing.OperatorAlgebra.H1UPoint.T0 P2MW.S_CuspForm_TWLevel_HeckeRing_OperatorAlgebra_exists_U_eigenvector_H1_of_algHom.CuspForm.TWLevel.HeckeRing.OperatorAlgebra.H1UPoint.BU P2MW.S_CuspForm_TWLevel_HeckeRing_OperatorAlgebra_exists_U_eigenvector_H1_of_algHom.CuspForm P2MW.S_CuspForm_TWLevel_HeckeRing_OperatorAlgebra_exists_U_eigenvector_H1_of_algHom.CuspForm.TWLevel"
p2m_reactivate "P2MW.S_CuspForm_TWLevel_HeckeRing_OperatorAlgebra_exists_U_eigenvector_H1_of_algHom.CuspForm.TWLevel.HeckeRing.OperatorAlgebra.H1UPoint.T0 P2MW.S_CuspForm_TWLevel_HeckeRing_OperatorAlgebra_exists_U_eigenvector_H1_of_algHom.CuspForm.TWLevel.HeckeRing.OperatorAlgebra.H1UPoint.BU P2MW.S_CuspForm_TWLevel_HeckeRing_OperatorAlgebra_exists_U_eigenvector_H1_of_algHom.CuspForm"

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
    (S : Set ℕ) (N : ℕ) [NeZero N] (r : ℕ) [NeZero r]
    (θ : CuspForm.heckeAlgebra N 2 S →+* ResidueField 𝒪)
    (t : ℕ) (qv : Fin t → ℕ) [∀ i, NeZero (qv i)] (α : Fin t → ResidueField 𝒪)
    (H : Subgroup (ZMod (level N r qv))ˣ)
    (hc : OpComm N r qv S 𝒪 H) (hdc : DiaComm N r qv S 𝒪 H)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra 𝒪 F]
    (hF : Function.Injective (algebraMap 𝒪 F))
    (lam : HeckeRing N r qv S 𝒪 H θ α hc hdc →ₐ[𝒪] F) :
    ∃ (e : (ZMod (level N r qv))ˣ →* Fˣ) (μ : Fin t → F) (c : CohCarrier.H1 (level N r qv) H F),
      c ≠ 0 ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ level N r qv),
        (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeT (level N r qv) H ℓ F c) =
          lam (HeckeRing.T N r qv S 𝒪 H θ α hc hdc ℓ hℓ hℓS hℓL) • c) ∧
      (∀ j : Fin t, CohCarrier.heckeT (level N r qv) H (qv j) F c = μ j • c) ∧
      (∀ u : (ZMod (level N r qv))ˣ,
        CohCarrier.diamondL (level N r qv) H F u c = ((e u : Fˣ) : F) • c) ∧
      (∀ (u : (ZMod (level N r qv))ˣ) (hu : u ∈ HR N r qv),
        ((e u : Fˣ) : F) = lam (HeckeRing.diamond N r qv S 𝒪 H θ α hc hdc u hu)) ∧
      (∀ u : (ZMod (level N r qv))ˣ, u ∈ H → e u = 1) ∧
      (∀ (j : Fin t) (a : 𝒪), IsLocalRing.residue 𝒪 a = α j →
        ∃ P : Polynomial 𝒪, P.Monic ∧ (∀ i < P.natDegree, P.coeff i ∈ maximalIdeal 𝒪) ∧
          Polynomial.aeval (μ j - algebraMap 𝒪 F a) P = 0) :=
  CuspForm.TWLevel.HeckeRing.OperatorAlgebra.H1UPoint.main S N r θ t qv α H hc hdc F hF lam

end S_CuspForm_TWLevel_HeckeRing_OperatorAlgebra_exists_U_eigenvector_H1_of_algHom
end P2MW
export P2MW.S_CuspForm_TWLevel_HeckeRing_OperatorAlgebra_exists_U_eigenvector_H1_of_algHom (solution)
