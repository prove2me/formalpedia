-- Prove2me | solution 1 for GaloisRepAdic.isFlatAt_of_ordinary_of_unitKummer_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/857def4d-81c3-5dee-bf17-fb41c7a80744

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_GaloisRep_exists_hopfAlgebra_withConv_equiv_of_ordinary_of_unitKummer_decomposition
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_isFlatAt_of_ordinary_of_unitKummer_decomposition
p2m_attr_erase "instance" "instIsScalarTowerTensorProduct_definitions"
p2m_attr_erase "simp" "closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff"

set_option autoImplicit false

namespace C7TopAux

variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W]

theorem repr_one_eq_zero_of_mem (e : Module.Basis (Fin 2) R W) {v : W} (hv : v ∈ R ∙ e 0) :
    e.repr v 1 = 0 := by
  obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hv
  simp

theorem eq_coords (e : Module.Basis (Fin 2) R W) (v : W) :
    v = e.repr v 0 • e 0 + e.repr v 1 • e 1 := by
  conv_lhs => rw [← e.sum_repr v]
  rw [Fin.sum_univ_two]

theorem det_eq_of_triangular (e : Module.Basis (Fin 2) R W) (f : W →ₗ[R] W) (x y z : R)
    (h0 : f (e 0) = x • e 0) (h1 : f (e 1) = y • e 0 + z • e 1) : LinearMap.det f = x * z := by
  classical
  rw [← LinearMap.det_toMatrix e, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, h0, h1]

theorem exists_coords (e : Module.Basis (Fin 2) R W) (f : W →ₗ[R] W) (hD : f (e 0) ∈ R ∙ e 0)
    (hI : ∀ v, f v - v ∈ R ∙ e 0) :
    ∃ x y : R, f (e 0) = x • e 0 ∧ f (e 1) = y • e 0 + e 1 := by
  refine ⟨e.repr (f (e 0)) 0, e.repr (f (e 1) - e 1) 0, ?_, ?_⟩
  · have h := eq_coords e (f (e 0))
    rw [repr_one_eq_zero_of_mem e hD, zero_smul, add_zero] at h
    exact h
  · have h := eq_coords e (f (e 1) - e 1)
    rw [repr_one_eq_zero_of_mem e (hI (e 1)), zero_smul, add_zero] at h
    rw [← sub_eq_iff_eq_add]
    exact h

end C7TopAux

open C7TopAux in
theorem solution
    {A : Type} [CommRing A] [IsLocalRing A] [Finite A] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (ρ : GaloisRepAdic A) (hdet : ρ.DetIsCyclotomic p)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (b : Module.Basis (Fin 2) A ρ.V)
    (hLD : ∀ σ ∈ P.decompositionSubgroup ℚ, ρ.ρ σ (b 0) ∈ A ∙ b 0)
    (hLI : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ σ v - v ∈ A ∙ b 0)
    (N : ℕ) (hN : (p : A) ^ N = 0)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (p ^ N))
    {t : ℕ} (u β : Fin t → AlgebraicClosure ℚ) (a : Fin t → A)
    (hu : ∀ i, P.valuation (u i) = 1) (huI : ∀ i, ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ (u i) = u i)
    (hβ : ∀ i, β i ^ p ^ N = u i)
    (hdec : ∀ τ ∈ P.inertiaSubgroupIn ℚ, (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ ξ = ξ) →
      ∀ k : Fin t → ℕ, (∀ i, τ (β i) = ζ ^ (k i) * β i) →
        ρ.ρ τ (b 1) - b 1 = (∑ i, (k i) • a i) • b 0) :
    ρ.IsFlatAt p := by
  classical
  have hp : p.Prime := Fact.out
  haveI : IsArtinianRing A := inferInstance

  obtain ⟨m, hm⟩ : ∃ m : ℕ, IsLocalRing.maximalIdeal A ^ m = 0 := by
    obtain ⟨m, hm⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hm
    exact ⟨m, hm⟩
  obtain ⟨F, hFfd, hFlev⟩ := ρ.isAdicContinuous m
  have hfix : ∀ σ ∈ F.fixingSubgroup, ∀ v : ρ.V, ρ.ρ σ v = v := by
    intro σ hσ v
    have h := hFlev σ ((IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ) v
    rw [hm, Ideal.zero_eq_bot, Submodule.bot_smul, Submodule.mem_bot, sub_eq_zero] at h
    exact h

  have hdetN : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ),
      (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ ξ = ξ ^ c) → LinearMap.det (ρ.ρ τ) = (c : A) := by
    intro τ c hc
    have h := hdet.2 N τ c hc
    rw [Nat.cast_pow, hN, Ideal.mem_span_singleton, zero_dvd_iff, sub_eq_zero] at h
    exact h

  have hb0 : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ c : ℕ,
      (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ ξ = ξ ^ c) → ρ.ρ τ (b 0) = (c : A) • b 0 := by
    intro τ hτ c hc
    have hτD : τ ∈ P.decompositionSubgroup ℚ := by
      obtain ⟨d, -, rfl⟩ := Subgroup.mem_map.mp hτ
      exact d.2
    obtain ⟨x, y, h0, h1⟩ := exists_coords b (ρ.ρ τ) (hLD τ hτD) (hLI τ hτ)
    have hdet' := det_eq_of_triangular b (ρ.ρ τ) x y 1 h0 (by rw [h1, one_smul])
    rw [mul_one, hdetN τ c hc] at hdet'
    rw [h0, ← hdet']
  refine ⟨Finite.of_surjective _ IsLocalRing.residue_surjective, fun I _ => ?_⟩

  haveI : Finite ρ.V := Module.finite_of_finite A
  let E : Type := ρ.V ⧸ (I • (⊤ : Submodule A ρ.V))
  let mk : ρ.V →ₗ[A] E := Submodule.mkQ _
  have hmk : Function.Surjective mk := Submodule.mkQ_surjective _
  haveI : Finite E := Finite.of_surjective mk hmk
  have hlev_apply : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : ρ.V),
      ρ.levelAction I σ (mk v) = mk (ρ.ρ σ v) := fun _ _ => rfl
  letI instE : DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) E :=
    { smul := fun σ x => ρ.levelAction I σ x
      one_smul := fun x => by
        obtain ⟨v, rfl⟩ := hmk x
        show ρ.levelAction I 1 (mk v) = mk v
        rw [hlev_apply, map_one, Module.End.one_apply]
      mul_smul := fun σ τ x => by
        obtain ⟨v, rfl⟩ := hmk x
        show ρ.levelAction I (σ * τ) (mk v) = ρ.levelAction I σ (ρ.levelAction I τ (mk v))
        rw [hlev_apply, hlev_apply, hlev_apply, map_mul, Module.End.mul_apply]
      smul_zero := fun σ => map_zero (ρ.levelAction I σ)
      smul_add := fun σ x y => map_add (ρ.levelAction I σ) x y }
  have hsmulE : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : ρ.V), σ • mk v = mk (ρ.ρ σ v) :=
    fun _ _ => rfl

  have hE : ∀ x : E, (p ^ N) • x = 0 := by
    intro x
    obtain ⟨v, rfl⟩ := hmk x
    rw [← map_nsmul, ← Nat.cast_smul_eq_nsmul A, Nat.cast_pow, hN, zero_smul, map_zero]
  have hlevE : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, ∀ x : E, s • x = x := by
    refine ⟨F, hFfd, fun s hs x => ?_⟩
    obtain ⟨v, rfl⟩ := hmk x
    rw [hsmulE, hfix s hs v]
  let L : Submodule A ρ.V := A ∙ b 0
  let E₁ : AddSubgroup E := (L.map mk).toAddSubgroup
  have hE₁mem : ∀ v : ρ.V, v ∈ L → mk v ∈ E₁ := fun v hv => Submodule.mem_map_of_mem hv
  have hE₁elim : ∀ y ∈ E₁, ∃ w ∈ L, mk w = y := fun y hy => Submodule.mem_map.mp hy
  have hE₁D : ∀ σ ∈ P.decompositionSubgroup ℚ, ∀ y ∈ E₁, σ • y ∈ E₁ := by
    intro σ hσ y hy
    obtain ⟨w, hw, rfl⟩ := hE₁elim y hy
    rw [hsmulE]
    apply hE₁mem
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [map_smul]
    exact Submodule.smul_mem _ c (hLD σ hσ)
  have hE₁I : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ c : ℕ,
      (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ ξ = ξ ^ c) → ∀ y ∈ E₁, τ • y = c • y := by
    intro τ hτ c hc y hy
    obtain ⟨w, hw, rfl⟩ := hE₁elim y hy
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [hsmulE, map_smul, hb0 τ hτ c hc, smul_comm, Nat.cast_smul_eq_nsmul, map_nsmul]
  have hEI : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ y : E, τ • y - y ∈ E₁ := by
    intro τ hτ y
    obtain ⟨v, rfl⟩ := hmk y
    rw [hsmulE, ← map_sub]
    exact hE₁mem _ (hLI τ hτ v)

  let ψ : Fin t → (ρ.V →ₗ[A] ρ.V) := fun i => (b.coord 1).smulRight (a i • b 0)
  have hψ_apply : ∀ i (v : ρ.V), ψ i v = b.repr v 1 • (a i • b 0) := fun _ _ => rfl
  have hψI : ∀ i, I • (⊤ : Submodule A ρ.V) ≤ (I • (⊤ : Submodule A ρ.V)).comap (ψ i) := by
    intro i
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  let φ : Fin t → (E →+ E) := fun i => (Submodule.mapQ _ _ (ψ i) (hψI i)).toAddMonoidHom
  have hφ_apply : ∀ i (v : ρ.V), φ i (mk v) = mk (ψ i v) := fun _ _ => rfl
  have hφ₁ : ∀ i (x : E), φ i x ∈ E₁ := by
    intro i x
    obtain ⟨v, rfl⟩ := hmk x
    rw [hφ_apply, hψ_apply, smul_smul]
    exact hE₁mem _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  have hφ₀ : ∀ i, ∀ y ∈ E₁, φ i y = 0 := by
    intro i y hy
    obtain ⟨w, hw, rfl⟩ := hE₁elim y hy
    rw [hφ_apply, hψ_apply, repr_one_eq_zero_of_mem b hw, zero_smul, map_zero]
  have hdecE : ∀ τ ∈ P.inertiaSubgroupIn ℚ, (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ ξ = ξ) →
      ∀ k : Fin t → ℕ, (∀ i, τ (β i) = ζ ^ (k i) * β i) → ∀ x : E, τ • x - x = ∑ i, (k i) • φ i x := by
    intro τ hτ hτμ k hk x
    obtain ⟨v, rfl⟩ := hmk x
    have h0 : ρ.ρ τ (b 0) = b 0 := by
      have := hb0 τ hτ 1 (fun ξ hξ => by rw [pow_one]; exact hτμ ξ hξ)
      rwa [Nat.cast_one, one_smul] at this
    have h1 := hdec τ hτ hτμ k hk
    have h1' : ρ.ρ τ (b 1) = (∑ i, (k i) • a i) • b 0 + b 1 := by
      rw [← sub_eq_iff_eq_add]; exact h1
    have hs : (∑ i, (k i) • a i : A) = ∑ i, ((k i : ℕ) : A) * a i :=
      Finset.sum_congr rfl fun i _ => nsmul_eq_mul _ _
    have hL : ρ.ρ τ v - v = (b.repr v 1 * ∑ i, ((k i : ℕ) : A) * a i) • b 0 := by
      conv_lhs => rw [eq_coords b v]
      rw [map_add, map_smul, map_smul, h0, h1', hs]
      module
    have hR : ∑ i, (k i) • ψ i v = (b.repr v 1 * ∑ i, ((k i : ℕ) : A) * a i) • b 0 := by
      rw [Finset.mul_sum, Finset.sum_smul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hψ_apply, ← Nat.cast_smul_eq_nsmul A (k i), smul_smul, smul_smul]
      congr 1
      ring
    have hv : ρ.ρ τ v - v = ∑ i, (k i) • ψ i v := hL.trans hR.symm
    rw [hsmulE, ← map_sub, hv, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_nsmul, hφ_apply]

  obtain ⟨H, _, _, hfin, hflat, hco, e, he_add, he_act⟩ :=
    GaloisRep.exists_hopfAlgebra_withConv_equiv_of_ordinary_of_unitKummer_decomposition p hp2 N E hE
      hlevE P hP E₁ hE₁D hE₁I hEI ζ hζ u β hu huI hβ φ hφ₁ hφ₀ hdecE
  exact ⟨H, ‹_›, ‹_›, hfin, hflat, hco, e, he_add, fun σ f g hfg => he_act σ f g hfg⟩

end S_GaloisRepAdic_isFlatAt_of_ordinary_of_unitKummer_decomposition
end P2MW
export P2MW.S_GaloisRepAdic_isFlatAt_of_ordinary_of_unitKummer_decomposition (solution)
