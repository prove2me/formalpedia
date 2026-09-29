-- Prove2me | solution 1 for FullLevelTate.Datum.isoHomGal_inertia_quadratic_of_specialization
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/d171511f-3793-5bc8-848b-a88730db8dff

import Definitions.Def_FullLevelTate_IsoHom
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_GaloisRep_TameCharacter
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.RingTheory.Norm.Defs
import Mathlib.Tactic.Module
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FullLevelTate_Datum_isoHomGal_inertia_quadratic_of_specialization

set_option autoImplicit false

namespace DrinfeldCurve
p2m_export "DrinfeldCurve" "x relation coe_hChar_apply hSubgroup mem_hSubgroup_iff"
p2m_open "DrinfeldCurve"

private theorem exists_mem_hSubgroup (q : ℕ) [Fact q.Prime] (α : (GaloisField q 2)ˣ) :
    ∃ g : CuspidalType.GL2 q, (g, α) ∈ hSubgroup q := by
  refine ⟨CuspidalType.torus q α⁻¹, ?_⟩
  rw [mem_hSubgroup_iff]
  refine Units.ext ?_
  rw [coe_hChar_apply, Units.val_one]
  dsimp only
  have hdet : ((CuspidalType.torus q α⁻¹ : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)).det =
      Algebra.norm (ZMod q) ((α⁻¹ : (GaloisField q 2)ˣ) : GaloisField q 2) := by
    rw [Algebra.norm_eq_matrix_det (CuspidalType.quadBasis q)]
    rfl
  have hnorm : algebraMap (ZMod q) (GaloisField q 2)
        (Algebra.norm (ZMod q) ((α⁻¹ : (GaloisField q 2)ˣ) : GaloisField q 2)) =
      ((α⁻¹ : (GaloisField q 2)ˣ) : GaloisField q 2) ^ (q + 1) := by
    rw [FiniteField.algebraMap_norm_eq_pow_sum, GaloisField.finrank q two_ne_zero]
    simp [Finset.sum_range_succ, add_comm]
  rw [hdet, hnorm, Units.val_inv_eq_inv_val, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ α.ne_zero)]

end DrinfeldCurve

namespace FLTateAsmDr

open scoped TensorProduct

private theorem pi_ne_zero_dr (q : ℕ) [Fact q.Prime] (π : AlgebraicClosure ℚ)
    (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) : π ≠ 0 := by
  rintro rfl
  have h2 : q ^ 2 - 1 ≠ 0 := by
    have hq : 2 ≤ q := (Fact.out : q.Prime).two_le
    have : 4 ≤ q ^ 2 := by nlinarith
    omega
  rw [zero_pow h2] at hπ
  exact (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero) hπ.symm

private theorem tameCharacter_one_dr (P : ValuationSubring (AlgebraicClosure ℚ)) (π : AlgebraicClosure ℚ)
    (hπ : π ≠ 0) : P.tameCharacter π 1 = 1 := by
  classical
  have h1 : (1 : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) π / π = 1 := by
    rw [AlgEquiv.one_apply, div_self hπ]
  have hmem : (1 : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) π / π ∈ P := by
    rw [h1]; exact P.one_mem
  unfold ValuationSubring.tameCharacter
  rw [dif_pos hmem]
  have : (⟨(1 : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) π / π, hmem⟩ : P) = 1 := Subtype.ext h1
  rw [this, map_one]

end FLTateAsmDr

open scoped TensorProduct

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) (O' : Type) [CommRing O'] [IsLocalRing O']
    (D : FullLevelTate.Datum q M' O')
    (K : Type) [Field K] [Algebra O' K]
    (θ : (GaloisField q 2)ˣ →* Kˣ) {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (σ : Representation K (CuspidalType.GL2 q) W) (hσ : CuspidalType.IsCuspidalOfType θ σ)
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ))
    (ι : GaloisField q 2 →+* IsLocalRing.ResidueField P)
    (T : Type) [AddCommGroup T] [Module K T] (ρT : ↥(DrinfeldCurve.hSubgroup q) →* Module.End K T)
    (hT : ∀ u : W →ₗ[K] T,
      (∀ (g : CuspidalType.GL2 q) (hg₁ : (g, (1 : (GaloisField q 2)ˣ)) ∈ DrinfeldCurve.hSubgroup q),
        u ∘ₗ σ g = ρT ⟨(g, 1), hg₁⟩ ∘ₗ u) →
      ∀ (α : (GaloisField q 2)ˣ) (g : CuspidalType.GL2 q) (hg : (g, α) ∈ DrinfeldCurve.hSubgroup q),
        let A : (W →ₗ[K] T) → (W →ₗ[K] T) := fun v => ρT ⟨(g, α), hg⟩ ∘ₗ v ∘ₗ σ g⁻¹
        A (A u) - (((θ α : Kˣ) : K) + ((θ (α ^ q) : Kˣ) : K)) • A u +
          (((θ α : Kˣ) : K) * ((θ (α ^ q) : Kˣ) : K)) • u = 0)
    (sp : K ⊗[O'] D.V →ₗ[K] T)
    (hsp : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ α : (GaloisField q 2)ˣ,
      ι (α : GaloisField q 2) = P.tameCharacter π τ →
        ∀ (g : CuspidalType.GL2 q) (hg : (g, α) ∈ DrinfeldCurve.hSubgroup q),
          sp ∘ₗ ((D.gl2 g * D.gal τ).baseChange K) = ρT ⟨(g, α), hg⟩ ∘ₗ sp)
    (U : Submodule K ↥(D.isoHom K (σ.comp (⊤ : Subgroup (CuspidalType.GL2 q)).subtype)))
    (hU : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ U,
      D.isoHomGal K (σ.comp (⊤ : Subgroup (CuspidalType.GL2 q)).subtype) τ f ∈ U)
    (hinj : ∀ f ∈ U,
      sp ∘ₗ (f : W →ₗ[K] K ⊗[O'] D.V) = 0 → f = 0) :
    ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ α : (GaloisField q 2)ˣ,
      ι (α : GaloisField q 2) = P.tameCharacter π τ →
        ∀ f ∈ U,
          ((D.isoHomGal K (σ.comp (⊤ : Subgroup (CuspidalType.GL2 q)).subtype) τ
                (D.isoHomGal K (σ.comp (⊤ : Subgroup (CuspidalType.GL2 q)).subtype) τ f) :
                ↥(D.isoHom K (σ.comp (⊤ : Subgroup (CuspidalType.GL2 q)).subtype))) :
              W →ₗ[K] K ⊗[O'] D.V) -
            (((θ α : Kˣ) : K) + ((θ (α ^ q) : Kˣ) : K)) •
              ((D.isoHomGal K (σ.comp (⊤ : Subgroup (CuspidalType.GL2 q)).subtype) τ f :
                  ↥(D.isoHom K (σ.comp (⊤ : Subgroup (CuspidalType.GL2 q)).subtype))) :
                W →ₗ[K] K ⊗[O'] D.V) +
            (((θ α : Kˣ) : K) * ((θ (α ^ q) : Kˣ) : K)) •
              ((f : ↥(D.isoHom K (σ.comp (⊤ : Subgroup (CuspidalType.GL2 q)).subtype))) :
                W →ₗ[K] K ⊗[O'] D.V) = 0 := by
  have _ := hσ
  intro τ hτ α hα f hf
  obtain ⟨g₀, hg₀⟩ := DrinfeldCurve.exists_mem_hSubgroup q α
  have hπ0 : π ≠ 0 := FLTateAsmDr.pi_ne_zero_dr q π hπ

  have hmem : ∀ φ : W →ₗ[K] K ⊗[O'] D.V, φ ∈ D.isoHom K (σ.comp (⊤ : Subgroup (CuspidalType.GL2 q)).subtype) →
      ∀ g : CuspidalType.GL2 q, φ ∘ₗ σ g = ((D.gl2 g).baseChange K) ∘ₗ φ :=
    fun φ hφ g => (D.mem_isoHom_iff K _ φ).1 hφ ⟨g, trivial⟩

  have htr : ∀ φ : W →ₗ[K] K ⊗[O'] D.V, φ ∈ D.isoHom K (σ.comp (⊤ : Subgroup (CuspidalType.GL2 q)).subtype) →
      sp ∘ₗ (((D.gal τ).baseChange K) ∘ₗ φ) = ρT ⟨(g₀, α), hg₀⟩ ∘ₗ (sp ∘ₗ φ) ∘ₗ σ g₀⁻¹ := by
    intro φ hφ
    have hE : D.gal τ = (D.gl2 g₀ * D.gal τ) * D.gl2 g₀⁻¹ := by
      rw [← D.gal_comm_gl2, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
    have h3 : ((D.gal τ).baseChange K) ∘ₗ φ = ((D.gl2 g₀ * D.gal τ).baseChange K) ∘ₗ (φ ∘ₗ σ g₀⁻¹) := by
      rw [hmem φ hφ g₀⁻¹, ← LinearMap.comp_assoc, ← Module.End.mul_eq_comp, ← LinearMap.baseChange_mul, ← hE]
    rw [h3, ← LinearMap.comp_assoc, hsp τ hτ α hα g₀ hg₀]
    simp only [LinearMap.comp_assoc]

  have hu : ∀ (g : CuspidalType.GL2 q) (hg₁ : (g, (1 : (GaloisField q 2)ˣ)) ∈ DrinfeldCurve.hSubgroup q),
      (sp ∘ₗ (f : W →ₗ[K] K ⊗[O'] D.V)) ∘ₗ σ g = ρT ⟨(g, 1), hg₁⟩ ∘ₗ (sp ∘ₗ (f : W →ₗ[K] K ⊗[O'] D.V)) := by
    intro g hg₁
    have h1 := hsp 1 (Subgroup.one_mem _) 1
      (by rw [Units.val_one, map_one, FLTateAsmDr.tameCharacter_one_dr P π hπ0]) g hg₁
    rw [map_one, mul_one] at h1
    rw [LinearMap.comp_assoc, hmem _ f.2 g, ← LinearMap.comp_assoc, h1, LinearMap.comp_assoc]

  have hq := hT (sp ∘ₗ (f : W →ₗ[K] K ⊗[O'] D.V)) hu α g₀ hg₀
  dsimp only at hq

  have hTf : D.isoHomGal K (σ.comp (⊤ : Subgroup (CuspidalType.GL2 q)).subtype) τ f ∈ U := hU τ hτ f hf
  have hTTf : D.isoHomGal K (σ.comp (⊤ : Subgroup (CuspidalType.GL2 q)).subtype) τ
      (D.isoHomGal K (σ.comp (⊤ : Subgroup (CuspidalType.GL2 q)).subtype) τ f) ∈ U := hU τ hτ _ hTf
  have hEmem : D.isoHomGal K (σ.comp (⊤ : Subgroup (CuspidalType.GL2 q)).subtype) τ
        (D.isoHomGal K (σ.comp (⊤ : Subgroup (CuspidalType.GL2 q)).subtype) τ f) +
      (-(((θ α : Kˣ) : K) + ((θ (α ^ q) : Kˣ) : K))) •
        D.isoHomGal K (σ.comp (⊤ : Subgroup (CuspidalType.GL2 q)).subtype) τ f +
      (((θ α : Kˣ) : K) * ((θ (α ^ q) : Kˣ) : K)) • f ∈ U :=
    U.add_mem (U.add_mem hTTf (U.smul_mem _ hTf)) (U.smul_mem _ hf)
  have hE0 := hinj _ hEmem (by
    rw [Submodule.coe_add, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, LinearMap.comp_add,
      LinearMap.comp_add, LinearMap.comp_smul, LinearMap.comp_smul,
      FullLevelTate.Datum.coe_isoHomGal_apply, htr _ (Subtype.property _),
      FullLevelTate.Datum.coe_isoHomGal_apply, htr _ f.2]
    rw [sub_eq_add_neg, ← neg_smul] at hq
    exact hq)
  have hcoe := congrArg
    (fun x : ↥(D.isoHom K (σ.comp (⊤ : Subgroup (CuspidalType.GL2 q)).subtype)) => (x : W →ₗ[K] K ⊗[O'] D.V)) hE0
  simp only [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_zero] at hcoe

  have key : ∀ (a b c : W →ₗ[K] K ⊗[O'] D.V) (r s : K), a + -r • b + s • c = 0 → a - r • b + s • c = 0 := by
    intro a b c r s h
    calc a - r • b + s • c = a + -r • b + s • c := by module
      _ = 0 := h
  exact key _ _ _ _ _ hcoe

end S_FullLevelTate_Datum_isoHomGal_inertia_quadratic_of_specialization
end P2MW
export P2MW.S_FullLevelTate_Datum_isoHomGal_inertia_quadratic_of_specialization (solution)
