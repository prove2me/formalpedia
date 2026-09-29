-- Prove2me | solution 1 for GaloisRep.tangentFinite_of_uniform_level
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/4d0f1521-46c6-592e-94e5-b5c1782a1560

import Definitions.Def_GaloisRep_DeformationCondition
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Flat
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_tangentFinite_of_uniform_level

set_option autoImplicit false

open IsLocalRing Module

open scoped TensorProduct

local notation "ℚ̄" => AlgebraicClosure ℚ

namespace WtTFSol

open GaloisRep

variable (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]

theorem tangentFinite_of_uniform_level [Finite (ResidueField 𝒪)]
    (ρbar : ResidualGaloisRep (ResidueField 𝒪))
    (𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop)
    (hM : ∃ M : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ M ∧
      letI : Algebra 𝒪 (DualNumber (ResidueField 𝒪)) :=
        ((algebraMap (ResidueField 𝒪) (DualNumber (ResidueField 𝒪))).comp
          (algebraMap 𝒪 (ResidueField 𝒪))).toAlgebra
      letI : Algebra (ResidueField 𝒪) (ResidueField (DualNumber (ResidueField 𝒪))) :=
        ((IsLocalRing.residue (DualNumber (ResidueField 𝒪))).comp
          (algebraMap (ResidueField 𝒪) (DualNumber (ResidueField 𝒪)))).toAlgebra
      ∀ ρ : GaloisRepAdic (DualNumber (ResidueField 𝒪)), 𝒟 ρ →
        ρ.residual.IsEquiv (ρbar.baseChange (ResidueField (DualNumber (ResidueField 𝒪)))) →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ M, σ x = x) → ρ.ρ σ = 1) :
    TangentFinite 𝒪 ρbar 𝒟 := by
  obtain ⟨M, hMfin, hlevel⟩ := hM
  unfold TangentFinite
  letI : Algebra 𝒪 (DualNumber (ResidueField 𝒪)) :=
    ((algebraMap (ResidueField 𝒪) (DualNumber (ResidueField 𝒪))).comp
      (algebraMap 𝒪 (ResidueField 𝒪))).toAlgebra
  letI : Algebra (ResidueField 𝒪) (ResidueField (DualNumber (ResidueField 𝒪))) :=
    ((IsLocalRing.residue (DualNumber (ResidueField 𝒪))).comp
      (algebraMap (ResidueField 𝒪) (DualNumber (ResidueField 𝒪)))).toAlgebra

  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert AlgebraicClosure.isAlgebraic ℚ
    rfl
    rfl
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
    { isAlgClosed := inferInstance, isAlgebraic := inferInstance }
  haveI : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
  haveI : IsGalois ℚ (AlgebraicClosure ℚ) := ⟨⟩
  haveI : M.fixingSubgroup.FiniteIndex :=
    ⟨by rw [← IntermediateField.finrank_eq_fixingSubgroup_index]; exact Module.finrank_pos.ne'⟩
  haveI : Finite ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ M.fixingSubgroup) :=
    M.fixingSubgroup.finite_quotient_of_finiteIndex

  haveI : Finite (DualNumber (ResidueField 𝒪)) :=
    Finite.of_equiv (ResidueField 𝒪 × ResidueField 𝒪) (Equiv.refl _)

  let Mat := Matrix (Fin 2) (Fin 2) (DualNumber (ResidueField 𝒪))
  let X := {ρ : GaloisRepAdic (DualNumber (ResidueField 𝒪)) //
    𝒟 ρ ∧ ρ.residual.IsEquiv (ρbar.baseChange (ResidueField (DualNumber (ResidueField 𝒪))))}
  let real : X → Set (((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ M.fixingSubgroup) → Mat) :=
    fun ρ => {m | ∃ b : Basis (Fin 2) (DualNumber (ResidueField 𝒪)) ρ.1.V,
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        m (QuotientGroup.mk σ) = LinearMap.toMatrix b b (ρ.1.ρ σ)}

  have real_le : ∀ (ρ ρ' : X) (e : GaloisRepAdic.Equiv ρ.1 ρ'.1), real ρ ⊆ real ρ' := by
    intro ρ ρ' e m ⟨b, hb⟩
    refine ⟨b.map e.toLinearEquiv, fun σ => ?_⟩
    rw [hb σ]
    refine Matrix.ext fun i j => ?_
    simp only [LinearMap.toMatrix_apply, Basis.map_apply, Basis.map_repr, LinearEquiv.trans_apply]
    rw [← e.map_apply, LinearEquiv.symm_apply_apply]
  have real_congr : ∀ ρ ρ' : X, ρ.1.IsEquiv ρ'.1 → real ρ = real ρ' := by
    intro ρ ρ' ⟨e⟩
    exact Set.Subset.antisymm (real_le ρ ρ' e) (real_le ρ' ρ e.symm)

  have real_nonempty : ∀ ρ : X, ∃ b : Basis (Fin 2) (DualNumber (ResidueField 𝒪)) ρ.1.V,
      (fun c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ M.fixingSubgroup =>
        Quotient.liftOn' c (fun σ => LinearMap.toMatrix b b (ρ.1.ρ σ)) (by
          intro σ σ' hσ
          rw [QuotientGroup.leftRel_apply] at hσ
          have h1 : ρ.1.ρ (σ⁻¹ * σ') = 1 :=
            hlevel ρ.1 ρ.2.1 ρ.2.2 _ (fun x hx => (IntermediateField.mem_fixingSubgroup_iff M _).mp hσ x hx)
          have hσ' : σ' = σ * (σ⁻¹ * σ') := by group
          show LinearMap.toMatrix b b (ρ.1.ρ σ) = LinearMap.toMatrix b b (ρ.1.ρ σ')
          rw [hσ', map_mul, h1, mul_one])) ∈ real ρ := by
    intro ρ
    refine ⟨Module.finBasisOfFinrankEq (DualNumber (ResidueField 𝒪)) ρ.1.V ρ.1.finrank_eq, ?_⟩
    exact ⟨_, fun σ => rfl⟩

  have equiv_of_real : ∀ ρ ρ' : X, real ρ = real ρ' → ρ.1.IsEquiv ρ'.1 := by
    intro ρ ρ' hreal
    obtain ⟨b, hb⟩ := real_nonempty ρ
    have hb' := hb
    rw [hreal] at hb'
    obtain ⟨b', hb'⟩ := hb'
    have hmat : ∀ σ, LinearMap.toMatrix b b (ρ.1.ρ σ) = LinearMap.toMatrix b' b' (ρ'.1.ρ σ) :=
      fun σ => hb' σ
    refine ⟨⟨b.equiv b' (Equiv.refl _), fun σ x => ?_⟩⟩
    have key : ((b.equiv b' (Equiv.refl _)).toLinearMap.comp (ρ.1.ρ σ)) =
        (ρ'.1.ρ σ).comp (b.equiv b' (Equiv.refl _)).toLinearMap := by
      refine b.ext fun j => ?_
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Basis.equiv_apply, Equiv.refl_apply]
      rw [← b.sum_repr (ρ.1.ρ σ (b j)), ← b'.sum_repr (ρ'.1.ρ σ (b' j))]
      simp only [map_sum, map_smul, Basis.equiv_apply, Equiv.refl_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      have := congrFun (congrFun (hmat σ) i) j
      simpa only [LinearMap.toMatrix_apply] using this
    exact LinearMap.congr_fun key x

  let Φ : Quotient (⟨fun ρ ρ' : X => ρ.1.IsEquiv ρ'.1, ⟨fun ρ => ⟨GaloisRepAdic.Equiv.refl ρ.1⟩,
      fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ => ⟨e.trans e'⟩⟩⟩ : Setoid X) →
      Set (((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ M.fixingSubgroup) → Mat) :=
    Quotient.lift real real_congr
  refine Finite.of_injective Φ ?_
  intro x y hxy
  induction x using Quotient.inductionOn with | h ρ => ?_
  induction y using Quotient.inductionOn with | h ρ' => ?_
  exact Quotient.sound (equiv_of_real ρ ρ' hxy)

end WtTFSol

p2m_open "IsLocalRing Module.IsLocalRing GaloisRep"

theorem solution (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    [Finite (ResidueField 𝒪)] (ρbar : ResidualGaloisRep (ResidueField 𝒪))
    (𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop)
    (hM : ∃ M : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ M ∧
      letI : Algebra 𝒪 (DualNumber (ResidueField 𝒪)) :=
        ((algebraMap (ResidueField 𝒪) (DualNumber (ResidueField 𝒪))).comp
          (algebraMap 𝒪 (ResidueField 𝒪))).toAlgebra
      letI : Algebra (ResidueField 𝒪) (ResidueField (DualNumber (ResidueField 𝒪))) :=
        ((IsLocalRing.residue (DualNumber (ResidueField 𝒪))).comp
          (algebraMap (ResidueField 𝒪) (DualNumber (ResidueField 𝒪)))).toAlgebra
      ∀ ρ : GaloisRepAdic (DualNumber (ResidueField 𝒪)), 𝒟 ρ →
        ρ.residual.IsEquiv (ρbar.baseChange (ResidueField (DualNumber (ResidueField 𝒪)))) →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ M, σ x = x) → ρ.ρ σ = 1) :
    TangentFinite 𝒪 ρbar 𝒟 :=
  WtTFSol.tangentFinite_of_uniform_level 𝒪 ρbar 𝒟 hM

end S_GaloisRep_tangentFinite_of_uniform_level
end P2MW
export P2MW.S_GaloisRep_tangentFinite_of_uniform_level (solution)
