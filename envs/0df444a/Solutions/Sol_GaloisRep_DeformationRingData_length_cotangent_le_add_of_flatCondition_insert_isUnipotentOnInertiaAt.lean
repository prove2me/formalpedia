-- Prove2me | solution 1 for GaloisRep.DeformationRingData.length_cotangent_le_add_of_flatCondition_insert_isUnipotentOnInertiaAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/f1bfe4ce-e171-5d14-bfea-00ce5a2651e1

import Definitions.Def_GaloisRep_DeformationRingData
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_Ramification
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Theorems.Thm_GaloisRep_DeformationRingData_length_cotangent_le_of_level_bounds
import Theorems.Thm_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnramifiedAt
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_pow_eq_frobConj
import Theorems.Thm_ValuationSubring_exists_tame_generator_inertiaSubgroupIn
import Theorems.Thm_GaloisRepAdic_isFlatAt_baseChangeAlong_of_finite_residueField
import Theorems.Thm_GaloisRepAdic_isUnipotentOnInertiaAt_baseChangeAlong
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_DeformationRingData_length_cotangent_le_add_of_flatCondition_insert_isUnipotentOnInertiaAt
p2m_attr_erase "instance" "instIsScalarTowerTensorProduct_definitions"
p2m_attr_erase "simp" "closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff"

set_option autoImplicit false

open scoped Pointwise TensorProduct

namespace FlatK1LC

open GaloisRepAdic

variable {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]

theorem equiv_conj_eq {ρ₁ ρ₂ : GaloisRepAdic A} (e : Equiv ρ₁ ρ₂)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ρ₂.ρ σ = (e.toLinearEquiv : ρ₁.V →ₗ[A] ρ₂.V) ∘ₗ ρ₁.ρ σ ∘ₗ
      (e.toLinearEquiv.symm : ρ₂.V →ₗ[A] ρ₁.V) := by
  refine LinearMap.ext fun y => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
    e.map_apply, LinearEquiv.apply_symm_apply]

theorem equiv_det_apply_eq {ρ₁ ρ₂ : GaloisRepAdic A} (e : Equiv ρ₁ ρ₂)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    LinearMap.det (ρ₂.ρ σ) = LinearMap.det (ρ₁.ρ σ) := by
  rw [equiv_conj_eq e σ, LinearMap.det_conj]

theorem det_apply_baseChangeAlong (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    LinearMap.det ((ρ.baseChangeAlong φ hφ).ρ σ) = φ (LinearMap.det (ρ.ρ σ)) := by
  letI : Algebra A B := φ.toAlgebra
  show LinearMap.det ((ρ.ρ σ).baseChange B) = algebraMap A B (LinearMap.det (ρ.ρ σ))
  exact LinearMap.det_baseChange (ρ.ρ σ)

theorem detIsCyclotomic_baseChangeAlong (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A)
    {p : ℕ} (h : ρ.DetIsCyclotomic p) : (ρ.baseChangeAlong φ hφ).DetIsCyclotomic p := by
  refine ⟨?_, fun n σ a hσ => ?_⟩
  · have hp : φ (p : A) ∈ IsLocalRing.maximalIdeal B := map_nonunit φ (p : A) h.1
    rwa [map_natCast] at hp
  · rw [det_apply_baseChangeAlong, Ideal.mem_span_singleton]
    have hdvd := map_dvd φ (Ideal.mem_span_singleton.mp (h.2 n σ a hσ))
    rwa [map_natCast, map_sub, map_natCast] at hdvd

theorem isUnramifiedAt_baseChangeAlong (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A)
    {q : ℕ} (h : ρ.IsUnramifiedAt q) : (ρ.baseChangeAlong φ hφ).IsUnramifiedAt q := by
  letI : Algebra A B := φ.toAlgebra
  intro P hP σ hσ
  show (ρ.ρ σ).baseChange B = 1
  rw [h P hP σ hσ, LinearMap.baseChange_one]

theorem finite_residueField_of_isLocalHom (φ : A →+* B) (hφ : IsLocalHom φ)
    (hB : Finite (IsLocalRing.ResidueField B)) : Finite (IsLocalRing.ResidueField A) :=
  haveI := hφ
  Finite.of_injective _ (IsLocalRing.ResidueField.map φ).injective

theorem guardedIsFlatAt_baseChangeAlong (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A)
    {p : ℕ} (h : Finite (IsLocalRing.ResidueField A) → ρ.IsFlatAt p) :
    Finite (IsLocalRing.ResidueField B) → (ρ.baseChangeAlong φ hφ).IsFlatAt p := fun hB =>
  haveI := hB
  GaloisRepAdic.isFlatAt_baseChangeAlong_of_finite_residueField φ hφ ρ
    (h (finite_residueField_of_isLocalHom φ hφ hB))

end FlatK1LC

namespace FlatK1Guard

open GaloisRep GaloisRepAdic

def guardedFlatCondition (𝒪 : Type) [CommRing 𝒪] (p : ℕ) (S : Finset ℕ) :
    ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop :=
  fun A _ _ _ ρ => ρ.DetIsCyclotomic p ∧ (Finite (IsLocalRing.ResidueField A) → ρ.IsFlatAt p) ∧
    ∀ q : ℕ, q.Prime → q ∉ S → ρ.IsUnramifiedAt q

def guardedFlatConditionU (𝒪 : Type) [CommRing 𝒪] (p : ℕ) (S U : Finset ℕ) :
    ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop :=
  fun A _ _ _ ρ => guardedFlatCondition 𝒪 p S ρ ∧ ∀ r ∈ U, r.Prime → r ≠ p → ρ.IsUnipotentOnInertiaAt r

variable (𝒪 : Type) [CommRing 𝒪] (p : ℕ)

theorem guarded_of_flat (S U : Finset ℕ) {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A]
    (ρ : GaloisRepAdic A) (h : flatCondition 𝒪 p S ρ ∧ ∀ r ∈ U, r.Prime → r ≠ p → ρ.IsUnipotentOnInertiaAt r) :
    guardedFlatConditionU 𝒪 p S U ρ :=
  ⟨⟨h.1.1, fun _ => h.1.2.1, h.1.2.2⟩, h.2⟩

theorem flat_of_guarded (S U : Finset ℕ) {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A]
    (ρ : GaloisRepAdic A) (hA : Finite (IsLocalRing.ResidueField A))
    (h : guardedFlatConditionU 𝒪 p S U ρ) :
    flatCondition 𝒪 p S ρ ∧ ∀ r ∈ U, r.Prime → r ≠ p → ρ.IsUnipotentOnInertiaAt r :=
  ⟨⟨h.1.1, h.1.2.1 hA, h.1.2.2⟩, h.2⟩

theorem hdet (S U : Finset ℕ) {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A]
    (ρ : GaloisRepAdic A) (h : guardedFlatConditionU 𝒪 p S U ρ) : ρ.DetIsCyclotomic p := h.1.1

theorem H1 (S U : Finset ℕ) {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A]
    (ρ : GaloisRepAdic A) {B : Type} [CommRing B] [IsLocalRing B] [Algebra 𝒪 B] (f : A →+* B)
    (hf : IsLocalHom f) (h : guardedFlatConditionU 𝒪 p S U ρ) :
    guardedFlatConditionU 𝒪 p S U (ρ.baseChangeAlong f hf) :=
  ⟨⟨FlatK1LC.detIsCyclotomic_baseChangeAlong f hf ρ h.1.1,
    FlatK1LC.guardedIsFlatAt_baseChangeAlong f hf ρ h.1.2.1,
    fun q hq hqS => FlatK1LC.isUnramifiedAt_baseChangeAlong f hf ρ (h.1.2.2 q hq hqS)⟩,
    fun r hrU hr hrp => GaloisRepAdic.isUnipotentOnInertiaAt_baseChangeAlong f hf ρ (h.2 r hrU hr hrp)⟩

theorem H2 (q : ℕ) (S U : Finset ℕ) {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A]
    (ρ : GaloisRepAdic A) (h : guardedFlatConditionU 𝒪 p (insert q S) U ρ)
    (hur : ∀ P' : ValuationSubring (AlgebraicClosure ℚ), P'.LiesOverPrime q →
      ∀ τ ∈ P'.inertiaSubgroupIn ℚ, ρ.ρ τ = 1) :
    guardedFlatConditionU 𝒪 p S U ρ := by
  refine ⟨⟨h.1.1, h.1.2.1, fun r hr hrS => ?_⟩, h.2⟩
  by_cases hrq : r = q
  · subst hrq; exact hur
  · exact h.1.2.2 r hr (fun hmem => (Finset.mem_insert.mp hmem).elim hrq hrS)

end FlatK1Guard

namespace FlatK1Reguard

open GaloisRep

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
  {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
  {𝒟 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}

omit [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] in

theorem finite_residueField_of_residue_surjective (A : Type) [CommRing A] [IsLocalRing A]
    [Algebra 𝒪 A] [IsLocalHom (algebraMap 𝒪 A)]
    (hres : Function.Surjective (IsLocalRing.residue A ∘ algebraMap 𝒪 A))
    (hfin : Finite (IsLocalRing.ResidueField 𝒪)) : Finite (IsLocalRing.ResidueField A) := by
  haveI := hfin
  refine Finite.of_surjective (IsLocalRing.ResidueField.map (algebraMap 𝒪 A)) fun y => ?_
  obtain ⟨x, rfl⟩ := hres y
  exact ⟨IsLocalRing.residue 𝒪 x, IsLocalRing.ResidueField.map_residue _ x⟩

theorem finite_residueField_base (D : DeformationRingData 𝒪 ρbar 𝒟)
    (h : Finite (IsLocalRing.ResidueField D.R)) : Finite (IsLocalRing.ResidueField 𝒪) :=
  FlatK1LC.finite_residueField_of_isLocalHom (algebraMap 𝒪 D.R) inferInstance h

noncomputable def reguard (D : DeformationRingData 𝒪 ρbar 𝒟)
    (hto : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρ : GaloisRepAdic A), 𝒟 ρ → 𝒟' ρ)
    (hfrom : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρ : GaloisRepAdic A),
      Finite (IsLocalRing.ResidueField A) → 𝒟' ρ → 𝒟 ρ)
    (hfin : Finite (IsLocalRing.ResidueField 𝒪)) : DeformationRingData 𝒪 ρbar 𝒟' where
  R := D.R
  residue_surjective := D.residue_surjective
  absIrr := D.absIrr
  ρ := D.ρ
  isOfType := hto D.ρ D.isOfType
  residual_isEquiv := D.residual_isEquiv
  universal A _ _ _ _ _ _ hres ρA hA hbar :=
    D.universal A hres ρA
      (hfrom ρA (finite_residueField_of_residue_surjective A hres hfin) hA) hbar

end FlatK1Reguard

open GaloisRep GaloisRepAdic FlatK1Guard

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp𝔪 : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪) (S U : Finset ℕ) (hpS : p ∈ S) (hqS : q ∉ S) (hUS : U ⊆ S)
    (D₀ : GaloisRep.DeformationRingData 𝒪 ρbar
      (fun ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρ : GaloisRepAdic A) =>
        GaloisRep.flatCondition 𝒪 p S ρ ∧ ∀ r ∈ U, r.Prime → r ≠ p → ρ.IsUnipotentOnInertiaAt r))
    (D' : GaloisRep.DeformationRingData 𝒪 ρbar
      (fun ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρ : GaloisRepAdic A) =>
        GaloisRep.flatCondition 𝒪 p (insert q S) ρ ∧ ∀ r ∈ U, r.Prime → r ≠ p → ρ.IsUnipotentOnInertiaAt r))
    (θ : D'.R →ₐ[𝒪] D₀.R) (x₀ : D₀.R →ₐ[𝒪] 𝒪)
    (hθ : IsLocalHom (θ : D'.R →+* D₀.R)) (hx₀ : IsLocalHom (x₀ : D₀.R →+* 𝒪))
    (hθρ : (D'.ρ.baseChangeAlong (θ : D'.R →+* D₀.R) hθ).IsEquiv D₀.ρ)
    (hθsurj : Function.Surjective θ)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : P.IsFrobeniusAt σ q)
    (hconj : ∀ P' : ValuationSubring (AlgebraicClosure ℚ), P'.LiesOverPrime q →
      ∃ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, g • P = P')
    (a : 𝒪)
    (hchar : (LinearMap.charpoly ((D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).ρ σ)) =
      Polynomial.X ^ 2 - Polynomial.C a * Polynomial.X + Polynomial.C ((q : 𝒪))) :
    Module.length 𝒪 (RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪)).Cotangent ≤
      Module.length 𝒪 (RingHom.ker x₀).Cotangent +
        Module.length 𝒪 (𝒪 ⧸ Ideal.span {((q : 𝒪) - 1) * (a ^ 2 - ((q : 𝒪) + 1) ^ 2)}) := by
  have _ := hpS
  have _ := hUS

  have hfin : Finite (IsLocalRing.ResidueField 𝒪) :=
    FlatK1Reguard.finite_residueField_base D₀ D₀.isOfType.1.2.1.1

  let G₀ : DeformationRingData 𝒪 ρbar (guardedFlatConditionU 𝒪 p S U) :=
    FlatK1Reguard.reguard D₀ (fun _ _ _ _ ρ h => guarded_of_flat 𝒪 p S U ρ h)
      (fun _ _ _ _ ρ hA h => flat_of_guarded 𝒪 p S U ρ hA h) hfin
  let G' : DeformationRingData 𝒪 ρbar (guardedFlatConditionU 𝒪 p (insert q S) U) :=
    FlatK1Reguard.reguard D' (fun _ _ _ _ ρ h => guarded_of_flat 𝒪 p (insert q S) U ρ h)
      (fun _ _ _ _ ρ hA h => flat_of_guarded 𝒪 p (insert q S) U ρ hA h) hfin

  have hur : (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).IsUnramifiedAt q :=
    FlatK1LC.isUnramifiedAt_baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀ D₀.ρ (D₀.isOfType.1.2.2 q hq hqS)

  exact GaloisRep.DeformationRingData.length_cotangent_le_of_level_bounds G₀ G' θ x₀ hθsurj _
    (fun n => GaloisRep.DeformationRingData.length_level_quotient_le_of_isUnramifiedAt
      G₀ G' θ x₀ p q hp hq hpq hp𝔪 hθ hx₀ hθρ hθsurj P hP σ hσ hconj a hchar hur
      (fun ρA h => FlatK1Guard.hdet 𝒪 p (insert q S) U ρA h)
      (fun ρA _ _ _ _ f hf h => FlatK1Guard.H1 𝒪 p (insert q S) U ρA f hf h)
      (fun ρA h hur' => FlatK1Guard.H2 𝒪 p q S U ρA h hur')
      (fun k τ hτ =>
        ValuationSubring.exists_mem_inertiaSubgroupIn_pow_eq_frobConj hp hq hpq P hP σ hσ k τ hτ)
      (fun m => ValuationSubring.exists_tame_generator_inertiaSubgroupIn hp hq hpq P hP m) n)

end S_GaloisRep_DeformationRingData_length_cotangent_le_add_of_flatCondition_insert_isUnipotentOnInertiaAt
end P2MW
export P2MW.S_GaloisRep_DeformationRingData_length_cotangent_le_add_of_flatCondition_insert_isUnipotentOnInertiaAt (solution)
