-- Prove2me | solution 1 for CerednikDrinfeld.evenAwayUnits_inf_levelSubgroup_exists_finset_orbits
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/4eac5196-9a3c-57d7-8fe9-d169ef2b43af

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_AlgFunctorConst
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Theorems.Thm_CerednikDrinfeld_evenAwayUnits_finite_stabilizer_vertex_and_exists_finset_orbits_of_not_dvd
import Theorems.Thm_CerednikDrinfeld_CosetGraph_finiteIndex_subgroupOf_inf_map_conj_awayUnits
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_evenAwayUnits_inf_levelSubgroup_exists_finset_orbits
p2m_attr_erase "instance" "ValuationSubring.mulSemiringActionWithVal ValuationSubring.mulSemiringActionCompletion ValuationSubring.uniformContinuousConstSMul_withVal ValuationSubring.charZero_completion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ValuationSubring.ratCast_mem_ratClosure ValuationSubring.intCast_mem_ratClosure ValuationSubring.natCast_mem_ratClosure QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField MatrixGroups
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.FormalOmega NeronModelInfra

namespace CocptT

theorem exists_finset_orbits_of_relIndex_ne_zero {G X : Type} [Group G] [MulAction G X]
    (H K : Subgroup G) (hKH : K ≤ H) (hfi : K.relIndex H ≠ 0)
    (S : Finset X) (hS : ∀ w : X, ∃ g ∈ H, g • w ∈ S) :
    ∃ S' : Finset X, ∀ w : X, ∃ k ∈ K, k • w ∈ S' := by
  classical
  haveI : (K.subgroupOf H).FiniteIndex := ⟨hfi⟩
  haveI : Finite (H ⧸ K.subgroupOf H) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (H ⧸ K.subgroupOf H) := Fintype.ofFinite _
  refine ⟨Finset.univ.biUnion fun q : H ⧸ K.subgroupOf H => S.image fun x => ((Quotient.out q : H) : G)⁻¹ • x, ?_⟩
  intro w
  obtain ⟨g, hg, hgw⟩ := hS w
  set q : H ⧸ K.subgroupOf H := QuotientGroup.mk ⟨g, hg⟩ with hq
  set t : H := Quotient.out q with htdef
  have ht : (QuotientGroup.mk t : H ⧸ K.subgroupOf H) = q := Quotient.out_eq q
  have hk : t⁻¹ * ⟨g, hg⟩ ∈ K.subgroupOf H := QuotientGroup.eq.mp (ht.trans hq)
  refine ⟨(t : G)⁻¹ * g, ?_, ?_⟩
  · simpa [Subgroup.mem_subgroupOf] using hk
  · rw [mul_smul]
    exact Finset.mem_biUnion.mpr ⟨q, Finset.mem_univ _, Finset.mem_image.mpr ⟨g • w, hgw, rfl⟩⟩

end CocptT

theorem solution

    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]

    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : 𝒪ˣ, (Matrix.GeneralLinearGroup.det g : K₀) = algebraMap 𝒪 K₀ (u : 𝒪) * (algebraMap 𝒪 K₀ π) ^ n)

    {rbar N : ℕ} [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrN : ¬ r ∣ N)
    {a₁ b₁ : ℚ} (hdef : IsDefiniteRamifiedExactlyAt (a := a₁) (b := b₁) rbar)
    (R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hR₁ : IsEichlerOrder R₁ N)
    (ι₀ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K₀) (hι₀ : Function.Injective ι₀)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (Γt : Subgroup (ℍ[ℚ, a₁, b₁])ˣ) (hΓt : ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, x ∈ Γt ↔ x ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v)
    (ρ₀ : (ℍ[ℚ, a₁, b₁])ˣ →* PGL(2, K₀))
    (hρ₀ : ∀ g : (ℍ[ℚ, a₁, b₁])ˣ, ρ₀ g = Matrix.ProjGenLinGroup.mk ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) g))
    (Γt' : Subgroup (ℍ[ℚ, a₁, b₁])ˣ)
    (hΓt' : ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, x ∈ Γt' ↔ x ∈ Γt ∧ Even (Multiplicative.toAdd (vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) x))))
    (Λ₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (n₁ : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (s : HeckeTower.AwayPrime r rbar → (ℍ[ℚ, a₁, b₁])ˣ)
    (sf : HeckeTower.AwayPrime r rbar → (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hs : ∀ ℓ : HeckeTower.AwayPrime r rbar,
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((r : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf ℓ : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
          (s ℓ : ℍ[ℚ, a₁, b₁]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ)) ∧
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((r : ℕ) : 𝓞 ℚ) ∈ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf ℓ : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) ∧
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a₁, b₁]
          (Units.map (algebraMap ℚ ℍ[ℚ, a₁, b₁]).toMonoidHom
            (Units.mk0 ((ℓ.1 : ℕ) : ℚ) (Nat.cast_ne_zero.mpr ℓ.1.prop.ne_zero))) * (sf ℓ)⁻¹ ∈
        (if (ℓ.1 : ℕ) ∣ N then levelHeckeUSet Λ₁ (meetOrder R₁ n₁) (ℓ.1 : ℕ)
          else primeHeckeSet (meetOrder R₁ n₁) (ℓ.1 : ℕ)) ∧
      nrd (s ℓ : ℍ[ℚ, a₁, b₁]) = ((ℓ.1 : ℕ) : ℚ))
    (Γtℓ : HeckeTower.AwayPrime r rbar → Subgroup (ℍ[ℚ, a₁, b₁])ˣ) (hΓtℓ : ∀ ℓ : HeckeTower.AwayPrime r rbar, Γtℓ ℓ = Γt ⊓ Γt.map (MulAut.conj (s ℓ)).toMonoidHom)
    (ℓ : HeckeTower.AwayPrime r rbar) :
    ∃ S : Finset (LT.LatticeTree.Vertex 𝒪 K₀), ∀ w : LT.LatticeTree.Vertex 𝒪 K₀, ∃ x ∈ (Γt' ⊓ Γtℓ ℓ).map ρ₀, x • w ∈ S := by
  classical
  obtain ⟨-, S, hS⟩ := CerednikDrinfeld.evenAwayUnits_finite_stabilizer_vertex_and_exists_finset_orbits_of_not_dvd
    𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr vdet hvdet hrr hrN hdef R₁ hR₁ ι₀ hι₀ v hv Γt hΓt ρ₀ hρ₀ Γt' hΓt'

  have hΓteq : Γt = CosetGraph.awayUnits R₁ v := Subgroup.ext hΓt
  have hfi0 : ((Γt ⊓ Γt.map (MulAut.conj (s ℓ)).toMonoidHom).subgroupOf Γt).FiniteIndex := by
    rw [hΓteq]; exact CerednikDrinfeld.CosetGraph.finiteIndex_subgroupOf_inf_map_conj_awayUnits hR₁.isOrder v hv (s ℓ)
  have h1 : (Γtℓ ℓ).relIndex Γt ≠ 0 := by
    rw [hΓtℓ ℓ]; exact hfi0.index_ne_zero
  have hle : Γt' ≤ Γt := fun x hx => ((hΓt' x).mp hx).1
  have h2 : (Γtℓ ℓ).relIndex Γt' ≠ 0 := fun h => h1 (Subgroup.relIndex_eq_zero_of_le_right hle h)
  have h3 : (Γt' ⊓ Γtℓ ℓ).relIndex Γt' ≠ 0 := by
    rwa [inf_comm, Subgroup.inf_relIndex_right]

  letI act : MulAction (ℍ[ℚ, a₁, b₁])ˣ (LT.LatticeTree.Vertex 𝒪 K₀) := MulAction.compHom _ ρ₀
  have hS' : ∀ w : LT.LatticeTree.Vertex 𝒪 K₀, ∃ g ∈ Γt', g • w ∈ S := by
    intro w
    obtain ⟨x, hx, hxw⟩ := hS w
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
    exact ⟨g, hg, hxw⟩
  obtain ⟨S', hS''⟩ := CocptT.exists_finset_orbits_of_relIndex_ne_zero Γt' (Γt' ⊓ Γtℓ ℓ) inf_le_left h3 S hS'
  refine ⟨S', fun w => ?_⟩
  obtain ⟨k, hk, hkw⟩ := hS'' w
  exact ⟨ρ₀ k, Subgroup.mem_map.mpr ⟨k, hk, rfl⟩, hkw⟩

end S_CerednikDrinfeld_evenAwayUnits_inf_levelSubgroup_exists_finset_orbits
end P2MW
export P2MW.S_CerednikDrinfeld_evenAwayUnits_inf_levelSubgroup_exists_finset_orbits (solution)
