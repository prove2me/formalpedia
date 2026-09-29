-- Prove2me | solution 1 for GaloisRep.DeformationRingData.exists_mem_adjoin_trace_frobenius_sub_mem_maximalIdeal_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/af0aa40d-e905-5332-bd74-fade267ff51b

import Mathlib
import Definitions.Def_GaloisRep_DeformationRingData
import Theorems.Thm_FrobeniusDensity_exists_isFrobeniusAt_conj_mem_of_le_ker
import Theorems.Thm_GaloisRepAdic_isEquiv_of_residual_isAbsolutelyIrreducible_of_trace_eq
import Theorems.Thm_GaloisRep_DeformationRingData_algHom_eq_of_isEquiv
import Theorems.Thm_ResidualGaloisRep_IsAbsolutelyIrreducible_baseChangeAlong
import Theorems.Thm_ResidualGaloisRep_isEquiv_of_isAbsolutelyIrreducible_of_charpoly_eq
import Theorems.Thm_ResidualGaloisRep_isAbsolutelyIrreducible_of_isAbsolutelyIrreducible_of_charpoly_eq
import Theorems.Thm_ResidualGaloisRep_charpoly_baseChangeAlong
import Theorems.Thm_GaloisRepAdic_charpoly_residual
import Theorems.Thm_GaloisRepAdic_charpoly_baseChangeAlong
import Theorems.Thm_GaloisRepAdic_trace_baseChangeAlong
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_DeformationRingData_exists_mem_adjoin_trace_frobenius_sub_mem_maximalIdeal_pow
p2m_attr_erase "instance" "FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false

namespace TGAsm

open IsLocalRing Polynomial

section General

variable {A : Type} [CommRing A]

theorem repr_mem_of_mem_smul_top {V : Type*} [AddCommGroup V] [Module A V] {ι : Type*}
    (b : Module.Basis ι A V) (I : Ideal A) {v : V} (hv : v ∈ I • (⊤ : Submodule A V)) (i : ι) :
    b.repr v i ∈ I := by
  refine Submodule.smul_induction_on hv (fun a ha w _ => ?_) (fun x y hx hy => ?_)
  · rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ ha
  · rw [map_add, Finsupp.add_apply]
    exact Ideal.add_mem _ hx hy

theorem trace_mem_of_forall_mem {V : Type*} [AddCommGroup V] [Module A V] [Module.Free A V]
    [Module.Finite A V] (I : Ideal A) (f : Module.End A V)
    (hf : ∀ v, f v ∈ I • (⊤ : Submodule A V)) : LinearMap.trace A V f ∈ I := by
  classical
  let b := Module.Free.chooseBasis A V
  rw [LinearMap.trace_eq_matrix_trace A b, Matrix.trace]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  exact repr_mem_of_mem_smul_top b I (hf _) i

theorem isAdicComplete_of_sq_eq_bot {R : Type*} [CommRing R] (I : Ideal R) (hI : I ^ 2 = ⊥) :
    IsAdicComplete I R := by
  have hpow : ∀ n, 2 ≤ n → (I ^ n • ⊤ : Submodule R R) = ⊥ := by
    intro n hn
    have : I ^ n = ⊥ := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
      rw [pow_add, hI, Ideal.bot_mul]
    rw [this, Submodule.bot_smul]
  have hH : IsHausdorff I R := ⟨fun x hx => by
    have h2 := hx 2
    rw [hpow 2 le_rfl, SModEq.bot] at h2
    exact h2⟩
  have hP : IsPrecomplete I R := ⟨fun {f} hf => by
    refine ⟨f 2, fun n => ?_⟩
    rcases le_or_gt n 2 with hn | hn
    · exact hf hn
    · have h := hf hn.le
      rw [hpow 2 le_rfl, SModEq.bot] at h
      rw [hpow n hn.le, SModEq.bot]
      exact h.symm⟩
  haveI := hH
  haveI := hP
  exact ⟨⟩

end General

section Residual

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
  {ρbar : ResidualGaloisRep (ResidueField 𝒪)}
  {𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}

theorem charpoly_eq_of_residualEquiv {k : Type} [Field k] {ρ₁ ρ₂ : ResidualGaloisRep k}
    (e : ResidualGaloisRep.Equiv ρ₁ ρ₂) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (ρ₁.ρ σ).charpoly = (ρ₂.ρ σ).charpoly := by
  have h : ρ₂.ρ σ = e.toLinearEquiv.conj (ρ₁.ρ σ) := by
    refine LinearMap.ext fun y => ?_
    rw [LinearEquiv.conj_apply_apply, e.map_apply, LinearEquiv.apply_symm_apply]
  rw [h, LinearEquiv.charpoly_conj]

theorem residual_baseChangeAlong (D : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟)
    {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] [IsLocalHom (algebraMap 𝒪 A)]
    (f : D.R →ₐ[𝒪] A) (hf : IsLocalHom (f : D.R →+* A)) :
    (D.ρ.baseChangeAlong (f : D.R →+* A) hf).residual.IsAbsolutelyIrreducible ∧
    (D.ρ.baseChangeAlong (f : D.R →+* A) hf).residual.IsEquiv
      (ρbar.baseChangeAlong (ResidueField.map (algebraMap 𝒪 A))) := by
  haveI := hf
  set ρA := D.ρ.baseChangeAlong (f : D.R →+* A) hf
  set ρbA := ρbar.baseChangeAlong (ResidueField.map (algebraMap 𝒪 A))
  have habs : ρbA.IsAbsolutelyIrreducible := D.absIrr.baseChangeAlong _

  have hcp : ∀ σ, (ρbA.ρ σ).charpoly = (ρA.residual.ρ σ).charpoly := by
    intro σ
    obtain ⟨eR⟩ := D.residual_isEquiv
    have h1 := GaloisRepAdic.charpoly_residual ρA σ
    have h2 := GaloisRepAdic.charpoly_baseChangeAlong (f : D.R →+* A) hf D.ρ σ
    have h3 := GaloisRepAdic.charpoly_residual D.ρ σ
    have h4 := charpoly_eq_of_residualEquiv eR σ
    have h5 := ResidualGaloisRep.charpoly_baseChangeAlong
      (ResidueField.map (algebraMap 𝒪 D.R)) ρbar σ
    have h6 := ResidualGaloisRep.charpoly_baseChangeAlong
      (ResidueField.map (algebraMap 𝒪 A)) ρbar σ

    have hcomp : (residue A).comp (f : D.R →+* A) = (ResidueField.map (f : D.R →+* A)).comp
        (residue D.R) := (IsLocalRing.ResidueField.map_comp_residue (f : D.R →+* A)).symm
    have hcomp' : ResidueField.map (algebraMap 𝒪 A) =
        (ResidueField.map (f : D.R →+* A)).comp (ResidueField.map (algebraMap 𝒪 D.R)) := by
      rw [← IsLocalRing.ResidueField.map_comp]
      congr 1
      exact (f.comp_algebraMap).symm
    change (ρbA.ρ σ).charpoly = _
    rw [h1, h2, Polynomial.map_map, hcomp, ← Polynomial.map_map, ← h3, h4, h5,
      Polynomial.map_map, ← hcomp', ← h6]
  have habsA : ρA.residual.IsAbsolutelyIrreducible :=
    ResidualGaloisRep.isAbsolutelyIrreducible_of_isAbsolutelyIrreducible_of_charpoly_eq _ _ habs hcp
  exact ⟨habsA, ResidualGaloisRep.isEquiv_of_isAbsolutelyIrreducible_of_charpoly_eq _ _ habsA habs
    fun σ => (hcp σ).symm⟩

end Residual

section Chebotarev

variable {A : Type} [CommRing A] [IsLocalRing A]

def levelStab (ρ : GaloisRepAdic A) (I : Ideal A) :
    Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) where
  carrier := {τ | ∀ v, ρ.ρ τ v - v ∈ I • (⊤ : Submodule A ρ.V)}
  one_mem' := fun v => by
    rw [map_one, Module.End.one_apply, sub_self]; exact Submodule.zero_mem _
  mul_mem' := fun {a b} ha hb v => by
    have h1 : ρ.ρ (a * b) v - v = ρ.ρ a (ρ.ρ b v - v) + (ρ.ρ a v - v) := by
      rw [map_mul, Module.End.mul_apply, map_sub]; abel
    rw [h1]
    refine Submodule.add_mem _ ?_ (ha v)
    have hmap : (I • (⊤ : Submodule A ρ.V)).map (ρ.ρ a) ≤ I • ⊤ := by
      rw [Submodule.map_smul'']; exact Submodule.smul_mono le_rfl le_top
    exact hmap (Submodule.mem_map_of_mem (hb v))
  inv_mem' := fun {a} ha v => by
    have h := ha (ρ.ρ a⁻¹ v)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h
    rw [← Submodule.neg_mem_iff, neg_sub]
    exact h

theorem mem_levelStab_iff (ρ : GaloisRepAdic A) (I : Ideal A)
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    τ ∈ levelStab ρ I ↔ ∀ v, ρ.ρ τ v - v ∈ I • (⊤ : Submodule A ρ.V) := Iff.rfl

theorem trace_sub_trace_mem (ρ : GaloisRepAdic A) (I : Ideal A)
    {τ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (h : τ * σ⁻¹ ∈ levelStab ρ I) :
    ρ.trace τ - ρ.trace σ ∈ I := by
  have hτ : τ = (τ * σ⁻¹) * σ := by group
  have hlin : ρ.ρ τ - ρ.ρ σ = (ρ.ρ (τ * σ⁻¹) - 1) * ρ.ρ σ := by
    conv_lhs => rw [hτ]
    rw [map_mul, sub_mul, one_mul]
  unfold GaloisRepAdic.trace
  rw [← map_sub, hlin]
  refine trace_mem_of_forall_mem I _ fun v => ?_
  rw [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply]
  exact h _

theorem trace_conj (ρ : GaloisRepAdic A) (g τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ρ.trace (g * τ * g⁻¹) = ρ.trace τ := by
  unfold GaloisRepAdic.trace
  rw [map_mul, LinearMap.trace_mul_comm, ← map_mul, ← mul_assoc, inv_mul_cancel, one_mul]

theorem exists_frobenius_trace_sub_mem (ρ : GaloisRepAdic A) (S : Finset ℕ) (n : ℕ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∉ S ∧ ∃ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ ∧
      ∃ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt τ ℓ ∧
        ρ.trace σ - ρ.trace τ ∈ (maximalIdeal A) ^ n := by
  obtain ⟨L, hLfin, hL⟩ := ρ.isAdicContinuous n
  haveI := hLfin
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := by convert AlgebraicClosure.instIsAlgClosure ℚ; rfl; rfl
  haveI : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ _
  haveI : FiniteDimensional ℚ (IntermediateField.normalClosure ℚ L (AlgebraicClosure ℚ)) :=
    normalClosure.is_finiteDimensional ℚ L (AlgebraicClosure ℚ)
  haveI : NumberField (IntermediateField.normalClosure ℚ L (AlgebraicClosure ℚ)) := ⟨⟩
  haveI : Normal ℚ (IntermediateField.normalClosure ℚ L (AlgebraicClosure ℚ)) :=
    normalClosure.normal ℚ L (AlgebraicClosure ℚ)
  haveI : IsGalois ℚ (IntermediateField.normalClosure ℚ L (AlgebraicClosure ℚ)) := ⟨⟩
  have hker : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ)
      (IntermediateField.normalClosure ℚ L (AlgebraicClosure ℚ))).ker ≤ levelStab ρ ((maximalIdeal A) ^ n) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    refine hL x fun y hy => ?_
    have h1 := AlgEquiv.restrictNormalHom_apply (IntermediateField.normalClosure ℚ L (AlgebraicClosure ℚ))
      x ⟨y, IntermediateField.le_normalClosure L hy⟩
    have h2 := DFunLike.congr_fun hx ⟨y, IntermediateField.le_normalClosure L hy⟩
    rw [AlgEquiv.one_apply] at h2
    have h3 := congrArg
      (fun z : ↥(IntermediateField.normalClosure ℚ L (AlgebraicClosure ℚ)) => (z : AlgebraicClosure ℚ)) h2
    exact h1.symm.trans h3
  obtain ⟨ℓ, P, τ, g, hℓ, hℓS, hP, hτ, hmem⟩ :=
    FrobeniusDensity.exists_isFrobeniusAt_conj_mem_of_le_ker
      (IntermediateField.normalClosure ℚ L (AlgebraicClosure ℚ)) hker S σ
  refine ⟨ℓ, hℓ, hℓS, P, hP, τ, hτ, ?_⟩
  have h := trace_sub_trace_mem ρ _ hmem
  rw [trace_conj] at h
  rw [← Submodule.neg_mem_iff, neg_sub]
  exact h

end Chebotarev

section Density

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
  {ρbar : ResidualGaloisRep (ResidueField 𝒪)}
  {𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
  (D : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟)

theorem residueField_map_bijective :
    Function.Bijective (ResidueField.map (algebraMap 𝒪 D.R)) := by
  refine ⟨RingHom.injective _, fun y => ?_⟩
  obtain ⟨a, ha⟩ := D.residue_surjective y
  exact ⟨residue 𝒪 a, ha⟩

noncomputable def r0 : D.R →+* ResidueField 𝒪 :=
  (RingEquiv.ofBijective _ (residueField_map_bijective D)).symm.toRingHom.comp (residue D.R)

theorem map_r0 (x : D.R) : ResidueField.map (algebraMap 𝒪 D.R) (r0 D x) = residue D.R x :=
  (RingEquiv.ofBijective _ (residueField_map_bijective D)).apply_symm_apply _

theorem r0_algebraMap (a : 𝒪) : r0 D (algebraMap 𝒪 D.R a) = residue 𝒪 a := by
  apply (residueField_map_bijective D).1
  rw [map_r0]
  rfl

theorem r0_eq_zero_iff (x : D.R) : r0 D x = 0 ↔ x ∈ maximalIdeal D.R := by
  rw [← residue_eq_zero_iff, ← map_r0]
  constructor
  · intro h; rw [h, map_zero]
  · intro h; exact (residueField_map_bijective D).1 (by rw [h, map_zero])

noncomputable def lift (x : D.R) : 𝒪 := Classical.choose (residue_surjective (r0 D x))

theorem residue_lift (x : D.R) : residue 𝒪 (lift D x) = r0 D x :=
  Classical.choose_spec (residue_surjective (r0 D x))

theorem sub_lift_mem (x : D.R) : x - algebraMap 𝒪 D.R (lift D x) ∈ maximalIdeal D.R := by
  rw [← r0_eq_zero_iff, map_sub, r0_algebraMap, residue_lift, sub_self]

noncomputable def ytr (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : D.R :=
  D.ρ.trace σ - algebraMap 𝒪 D.R (lift D (D.ρ.trace σ))

theorem ytr_mem_maximalIdeal (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ytr D σ ∈ maximalIdeal D.R := sub_lift_mem D _

noncomputable def B0 : Subalgebra 𝒪 D.R :=
  Algebra.adjoin 𝒪 (Set.range fun σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ => D.ρ.trace σ)

theorem ytr_mem_B0 (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : ytr D σ ∈ B0 D :=
  Subalgebra.sub_mem _ (Algebra.subset_adjoin ⟨σ, rfl⟩) (Subalgebra.algebraMap_mem _ _)

noncomputable def K : Ideal D.R :=
  (maximalIdeal D.R) ^ 2 ⊔ (maximalIdeal 𝒪).map (algebraMap 𝒪 D.R) ⊔ Ideal.span (Set.range (ytr D))

theorem K_le : K D ≤ maximalIdeal D.R := by
  refine sup_le (sup_le ?_ (map_maximalIdeal_le _)) ?_
  · exact Ideal.pow_le_self two_ne_zero
  · rw [Ideal.span_le]; rintro _ ⟨σ, rfl⟩; exact ytr_mem_maximalIdeal D σ

theorem K_ne_top : K D ≠ ⊤ := fun h =>
  (maximalIdeal.isMaximal D.R).ne_top (top_le_iff.mp (h ▸ K_le D))

scoped instance : Nontrivial (D.R ⧸ K D) := Ideal.Quotient.nontrivial_iff.mpr (K_ne_top D)

scoped instance : IsLocalRing (D.R ⧸ K D) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk (K D)) Ideal.Quotient.mk_surjective

theorem isLocalHom_mk : IsLocalHom (Ideal.Quotient.mk (K D)) := by
  refine ⟨fun x hx => ?_⟩
  by_contra hxu
  have hxm : x ∈ maximalIdeal D.R := hxu
  obtain ⟨u, hu⟩ := hx
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (↑u⁻¹ : D.R ⧸ K D)
  have h1 : Ideal.Quotient.mk (K D) (x * y) = 1 := by rw [map_mul, ← hu, hy, Units.mul_inv]
  rw [← (Ideal.Quotient.mk (K D)).map_one, Ideal.Quotient.eq] at h1
  have h2 : x * y - 1 ∈ maximalIdeal D.R := K_le D h1
  have h3 : (1 : D.R) ∈ maximalIdeal D.R := by
    have := Ideal.sub_mem _ (Ideal.mul_mem_right y _ hxm) h2
    rwa [sub_sub_cancel] at this
  exact (maximalIdeal.isMaximal D.R).ne_top (Ideal.eq_top_of_isUnit_mem _ h3 isUnit_one)

theorem mem_maximalIdeal_quot_iff (z : D.R ⧸ K D) :
    z ∈ maximalIdeal (D.R ⧸ K D) ↔ ∃ x ∈ maximalIdeal D.R, Ideal.Quotient.mk (K D) x = z := by
  constructor
  · intro hz
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    refine ⟨x, ?_, rfl⟩
    by_contra hx
    exact hz ((IsUnit.map (Ideal.Quotient.mk (K D))) (not_not.mp fun h => hx h))
  · rintro ⟨x, hx, rfl⟩
    haveI := isLocalHom_mk D
    exact map_nonunit (Ideal.Quotient.mk (K D)) x hx

theorem maximalIdeal_quot_sq : (maximalIdeal (D.R ⧸ K D)) ^ 2 = ⊥ := by
  rw [pow_two, ← le_bot_iff, Ideal.mul_le]
  intro a ha b hb
  obtain ⟨x, hx, rfl⟩ := (mem_maximalIdeal_quot_iff D a).mp ha
  obtain ⟨y, hy, rfl⟩ := (mem_maximalIdeal_quot_iff D b).mp hb
  rw [Ideal.mem_bot, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  refine le_sup_left (α := Ideal D.R) (le_sup_left (α := Ideal D.R) ?_)
  rw [pow_two]
  exact Ideal.mul_mem_mul hx hy

scoped instance : IsAdicComplete (maximalIdeal (D.R ⧸ K D)) (D.R ⧸ K D) :=
  isAdicComplete_of_sq_eq_bot _ (maximalIdeal_quot_sq D)

scoped instance : IsLocalHom (algebraMap 𝒪 (D.R ⧸ K D)) := by
  have : algebraMap 𝒪 (D.R ⧸ K D) = (Ideal.Quotient.mk (K D)).comp (algebraMap 𝒪 D.R) := rfl
  rw [this]
  haveI := isLocalHom_mk D
  exact RingHom.isLocalHom_comp _ _

theorem residue_quot_surjective :
    Function.Surjective (residue (D.R ⧸ K D) ∘ algebraMap 𝒪 (D.R ⧸ K D)) := by
  intro z
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨lift D x, ?_⟩
  change residue _ (Ideal.Quotient.mk (K D) (algebraMap 𝒪 D.R (lift D x))) = residue _ _
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, ← map_sub]
  haveI := isLocalHom_mk D
  refine map_nonunit (Ideal.Quotient.mk (K D)) _ ?_
  rw [← neg_sub]
  exact (Submodule.neg_mem_iff _).mpr (sub_lift_mem D x)

theorem maximalIdeal_le_comap_K : maximalIdeal 𝒪 ≤ (K D).comap (algebraMap 𝒪 D.R) := by
  rw [← Ideal.map_le_iff_le_comap]
  exact le_sup_of_le_left le_sup_right

noncomputable def algk : ResidueField 𝒪 →+* D.R ⧸ K D :=
  Ideal.quotientMap (K D) (algebraMap 𝒪 D.R) (maximalIdeal_le_comap_K D)

theorem algk_residue (a : 𝒪) : algk D (residue 𝒪 a) = Ideal.Quotient.mk (K D) (algebraMap 𝒪 D.R a) :=
  rfl

noncomputable def π4 : D.R →ₐ[𝒪] D.R ⧸ K D := Ideal.Quotient.mkₐ 𝒪 (K D)

noncomputable def π0 : D.R →ₐ[𝒪] D.R ⧸ K D :=
  { (algk D).comp (r0 D) with
    commutes' := fun a => by
      change algk D (r0 D (algebraMap 𝒪 D.R a)) = Ideal.Quotient.mk (K D) (algebraMap 𝒪 D.R a)
      rw [r0_algebraMap, algk_residue] }

theorem π4_apply (x : D.R) : π4 D x = Ideal.Quotient.mk (K D) x := rfl

theorem π0_apply (x : D.R) : π0 D x = algk D (r0 D x) := rfl

theorem isLocalHom_π4 : IsLocalHom (π4 D : D.R →+* D.R ⧸ K D) := isLocalHom_mk D

theorem isLocalHom_π0 : IsLocalHom (π0 D : D.R →+* D.R ⧸ K D) := by
  refine ⟨fun x hx => ?_⟩
  by_contra hxu
  have hxm : x ∈ maximalIdeal D.R := hxu
  have h0 : (π0 D : D.R →+* D.R ⧸ K D) x = 0 := by
    change algk D (r0 D x) = 0
    rw [(r0_eq_zero_iff D x).mpr hxm, map_zero]
  rw [h0] at hx
  exact not_isUnit_zero hx

theorem π0_trace_eq (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    π0 D (D.ρ.trace σ) = π4 D (D.ρ.trace σ) := by
  have hsplit : D.ρ.trace σ = algebraMap 𝒪 D.R (lift D (D.ρ.trace σ)) + ytr D σ := by
    unfold ytr; abel
  have hy0 : Ideal.Quotient.mk (K D) (ytr D σ) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (le_sup_right (α := Ideal D.R) (Ideal.subset_span ⟨σ, rfl⟩))
  rw [π0_apply, ← residue_lift, algk_residue, π4_apply]
  conv_rhs => rw [hsplit, map_add, hy0, add_zero]

theorem maximalIdeal_le_K
    (h𝒟 : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
        [IsAdicComplete (maximalIdeal A) A] [Algebra 𝒪 A] [IsLocalHom (algebraMap 𝒪 A)],
        Function.Surjective (residue A ∘ algebraMap 𝒪 A) →
        ∀ (f : D.R →ₐ[𝒪] A) (hf : IsLocalHom (f : D.R →+* A)),
          𝒟 (D.ρ.baseChangeAlong (f : D.R →+* A) hf)) :
    maximalIdeal D.R ≤ K D := by
  have hA := residue_quot_surjective D
  set ρA := D.ρ.baseChangeAlong (π4 D : D.R →+* D.R ⧸ K D) (isLocalHom_π4 D)
  have hres := residual_baseChangeAlong D (π4 D) (isLocalHom_π4 D)
  have hres0 := residual_baseChangeAlong D (π0 D) (isLocalHom_π0 D)

  have e₂ : (D.ρ.baseChangeAlong (π0 D : D.R →+* D.R ⧸ K D) (isLocalHom_π0 D)).IsEquiv ρA := by
    refine GaloisRepAdic.isEquiv_of_residual_isAbsolutelyIrreducible_of_trace_eq _ _ hres0.1 hres.1
      fun σ => ?_
    rw [GaloisRepAdic.trace_baseChangeAlong, GaloisRepAdic.trace_baseChangeAlong]
    exact π0_trace_eq D σ
  have e₁ : ρA.IsEquiv ρA := ⟨GaloisRepAdic.Equiv.refl _⟩
  have heq := GaloisRep.DeformationRingData.algHom_eq_of_isEquiv D (D.R ⧸ K D) hA ρA
    (h𝒟 _ hA (π4 D) (isLocalHom_π4 D)) hres.2 (π4 D) (π0 D) (isLocalHom_π4 D) (isLocalHom_π0 D) e₁ e₂
  intro x hx
  have h1 : π4 D x = 0 := by
    rw [heq, π0_apply, (r0_eq_zero_iff D x).mpr hx, map_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.mp h1

theorem exists_mem_B0_sub_mem_sq_of_mem_span {T : Set D.R} (hT : ∀ z ∈ T, z ∈ B0 D ∧ z ∈ maximalIdeal D.R)
    {w : D.R} (hw : w ∈ Ideal.span T) :
    ∃ y ∈ B0 D, y ∈ maximalIdeal D.R ∧ w - y ∈ (maximalIdeal D.R) ^ 2 := by
  induction hw using Submodule.span_induction with
  | mem z hz => exact ⟨z, (hT z hz).1, (hT z hz).2, by rw [sub_self]; exact Ideal.zero_mem _⟩
  | zero => exact ⟨0, Subalgebra.zero_mem _, Ideal.zero_mem _, by rw [sub_self]; exact Ideal.zero_mem _⟩
  | add u v _ _ hu hv =>
    obtain ⟨y₁, h₁B, h₁m, h₁⟩ := hu
    obtain ⟨y₂, h₂B, h₂m, h₂⟩ := hv
    refine ⟨y₁ + y₂, Subalgebra.add_mem _ h₁B h₂B, Ideal.add_mem _ h₁m h₂m, ?_⟩
    have : u + v - (y₁ + y₂) = (u - y₁) + (v - y₂) := by abel
    rw [this]; exact Ideal.add_mem _ h₁ h₂
  | smul r u _ hu =>
    obtain ⟨y, hyB, hym, hy⟩ := hu
    have hum : u ∈ maximalIdeal D.R := by
      have := Ideal.add_mem _ (Ideal.pow_le_self two_ne_zero hy) hym
      rwa [sub_add_cancel] at this
    refine ⟨algebraMap 𝒪 D.R (lift D r) * y,
      Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) hyB, Ideal.mul_mem_left _ _ hym, ?_⟩
    have hsplit : r • u - algebraMap 𝒪 D.R (lift D r) * y =
        (r - algebraMap 𝒪 D.R (lift D r)) * u + algebraMap 𝒪 D.R (lift D r) * (u - y) := by
      rw [smul_eq_mul]; ring
    rw [hsplit, pow_two]
    exact Ideal.add_mem _ (Ideal.mul_mem_mul (sub_lift_mem D r) hum)
      (Ideal.mul_mem_left _ _ (by rw [← pow_two]; exact hy))

theorem exists_mem_B0_sub_mem_sq (hK : maximalIdeal D.R ≤ K D) {x : D.R} (hx : x ∈ maximalIdeal D.R) :
    ∃ y ∈ B0 D, y ∈ maximalIdeal D.R ∧ x - y ∈ (maximalIdeal D.R) ^ 2 := by
  have hxK := hK hx
  unfold K at hxK
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hxK
  obtain ⟨u₂, hu₂, uϖ, huϖ, rfl⟩ := Submodule.mem_sup.mp hu

  obtain ⟨y₁, h₁B, h₁m, h₁⟩ := exists_mem_B0_sub_mem_sq_of_mem_span D
    (T := algebraMap 𝒪 D.R '' (maximalIdeal 𝒪 : Set 𝒪)) (fun z hz => by
      obtain ⟨c, hc, rfl⟩ := hz
      exact ⟨Subalgebra.algebraMap_mem _ _, map_nonunit _ c hc⟩) huϖ
  obtain ⟨y₂, h₂B, h₂m, h₂⟩ := exists_mem_B0_sub_mem_sq_of_mem_span D (T := Set.range (ytr D))
    (fun z hz => by obtain ⟨σ, rfl⟩ := hz; exact ⟨ytr_mem_B0 D σ, ytr_mem_maximalIdeal D σ⟩) hw
  refine ⟨y₁ + y₂, Subalgebra.add_mem _ h₁B h₂B, Ideal.add_mem _ h₁m h₂m, ?_⟩
  have : u₂ + uϖ + w - (y₁ + y₂) = u₂ + ((uϖ - y₁) + (w - y₂)) := by abel
  rw [this]
  exact Ideal.add_mem _ hu₂ (Ideal.add_mem _ h₁ h₂)

theorem exists_mem_B0_sub_mem_pow_succ (hK : maximalIdeal D.R ≤ K D) (j : ℕ) {x : D.R}
    (hx : x ∈ (maximalIdeal D.R) ^ j) : ∃ b ∈ B0 D, x - b ∈ (maximalIdeal D.R) ^ (j + 1) := by
  induction j generalizing x with
  | zero =>
    exact ⟨algebraMap 𝒪 D.R (lift D x), Subalgebra.algebraMap_mem _ _, by
      rw [zero_add, pow_one]; exact sub_lift_mem D x⟩
  | succ j ih =>
    rw [pow_succ'] at hx
    refine Submodule.mul_induction_on hx (fun m hm z hz => ?_) (fun u v hu hv => ?_)
    · obtain ⟨y, hyB, hym, hy⟩ := exists_mem_B0_sub_mem_sq D hK hm
      obtain ⟨b, hbB, hb⟩ := ih hz
      refine ⟨y * b, Subalgebra.mul_mem _ hyB hbB, ?_⟩
      have hsplit : m * z - y * b = (m - y) * z + y * (z - b) := by ring
      rw [hsplit]
      refine Ideal.add_mem _ ?_ ?_
      · have := Ideal.mul_mem_mul hy hz
        rwa [← pow_add, show 2 + j = j + 1 + 1 by omega] at this
      · have := Ideal.mul_mem_mul hym hb
        rwa [← pow_succ'] at this
    · obtain ⟨b₁, h₁B, h₁⟩ := hu
      obtain ⟨b₂, h₂B, h₂⟩ := hv
      refine ⟨b₁ + b₂, Subalgebra.add_mem _ h₁B h₂B, ?_⟩
      have : u + v - (b₁ + b₂) = (u - b₁) + (v - b₂) := by abel
      rw [this]; exact Ideal.add_mem _ h₁ h₂

theorem exists_mem_B0_sub_mem_pow (hK : maximalIdeal D.R ≤ K D) (n : ℕ) (x : D.R) :
    ∃ b ∈ B0 D, x - b ∈ (maximalIdeal D.R) ^ n := by
  induction n with
  | zero => exact ⟨0, Subalgebra.zero_mem _, by rw [pow_zero, Ideal.one_eq_top]; trivial⟩
  | succ n ih =>
    obtain ⟨b₁, h₁B, h₁⟩ := ih
    obtain ⟨b₂, h₂B, h₂⟩ := exists_mem_B0_sub_mem_pow_succ D hK n h₁
    refine ⟨b₁ + b₂, Subalgebra.add_mem _ h₁B h₂B, ?_⟩
    rwa [← sub_sub]

end Density

end TGAsm
p2m_reactivate "P2MW.S_GaloisRep_DeformationRingData_exists_mem_adjoin_trace_frobenius_sub_mem_maximalIdeal_pow.TGAsm"

open IsLocalRing

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    {𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (D : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟)
    (h𝒟 : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
        [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [Algebra 𝒪 A] [IsLocalHom (algebraMap 𝒪 A)],
        Function.Surjective (IsLocalRing.residue A ∘ algebraMap 𝒪 A) →
        ∀ (f : D.R →ₐ[𝒪] A) (hf : IsLocalHom (f : D.R →+* A)),
          𝒟 (D.ρ.baseChangeAlong (f : D.R →+* A) hf))
    (S : Finset ℕ) (n : ℕ) (x : D.R) :
    ∃ b ∈ Algebra.adjoin 𝒪 {y : D.R | ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∉ S ∧
        ∃ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ ∧
          ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ ∧ y = D.ρ.trace σ},
      x - b ∈ IsLocalRing.maximalIdeal D.R ^ n := by
  set TF : Set D.R := {y : D.R | ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∉ S ∧
        ∃ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ ∧
          ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ ∧ y = D.ρ.trace σ}

  have hK := TGAsm.maximalIdeal_le_K D h𝒟
  obtain ⟨b, hb, hxb⟩ := TGAsm.exists_mem_B0_sub_mem_pow D hK n x

  let q : D.R →ₐ[𝒪] D.R ⧸ (maximalIdeal D.R) ^ n := Ideal.Quotient.mkₐ 𝒪 _
  have hle : (TGAsm.B0 D).map q ≤ (Algebra.adjoin 𝒪 TF).map q := by
    unfold TGAsm.B0
    rw [AlgHom.map_adjoin, AlgHom.map_adjoin]
    refine Algebra.adjoin_mono ?_
    rintro _ ⟨_, ⟨σ, rfl⟩, rfl⟩
    obtain ⟨ℓ, hℓ, hℓS, P, hP, τ, hτ, hστ⟩ := TGAsm.exists_frobenius_trace_sub_mem D.ρ S n σ
    refine ⟨D.ρ.trace τ, ⟨ℓ, hℓ, hℓS, P, hP, τ, hτ, rfl⟩, ?_⟩
    exact ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr hστ).symm
  obtain ⟨b', hb', hbb'⟩ := Subalgebra.mem_map.mp (hle (Subalgebra.mem_map.mpr ⟨b, hb, rfl⟩))
  refine ⟨b', hb', ?_⟩
  have h2 : b - b' ∈ (maximalIdeal D.R) ^ n := (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hbb'.symm
  have : x - b' = (x - b) + (b - b') := by abel
  rw [this]
  exact Ideal.add_mem _ hxb h2

end S_GaloisRep_DeformationRingData_exists_mem_adjoin_trace_frobenius_sub_mem_maximalIdeal_pow
end P2MW
export P2MW.S_GaloisRep_DeformationRingData_exists_mem_adjoin_trace_frobenius_sub_mem_maximalIdeal_pow (solution)
