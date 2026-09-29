-- Prove2me | solution 1 for GaloisRep.DeformationRingData.exists_patchingDatum_of_ladder
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/1498e865-7d81-597e-9674-37bc0bdb5b61

import Definitions.Def_GaloisRep_DeformationRingData
import Theorems.Thm_Algebra_PatchingDatum_nonempty_of_exists_presentation_of_free
import Theorems.Thm_Algebra_PatchingDatum_bijective_and_free_of_surjective
import Theorems.Thm_AlgHom_bijective_and_free_of_length_le_of_levelChange
import Theorems.Thm_AlgHom_length_cotangent_mul_eq_length_quotient_of_free
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_DeformationRingData_exists_patchingDatum_of_ladder

private theorem levelLoweringMap_aux
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A],
      GaloisRepAdic A → Prop}
    (h : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A]
      (ρ : GaloisRepAdic A), 𝒟₀ ρ → 𝒟' ρ)
    (D₀ : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟₀)
    (D' : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟') :
    ∃ θ : D'.R →ₐ[𝒪] D₀.R, ∃ hθ : IsLocalHom (θ : D'.R →+* D₀.R),
      (D'.ρ.baseChangeAlong (θ : D'.R →+* D₀.R) hθ).IsEquiv D₀.ρ := by
  obtain ⟨θ, hθ, -⟩ :=
    D'.universal D₀.R D₀.residue_surjective D₀.ρ (h D₀.ρ D₀.isOfType) D₀.residual_isEquiv
  exact ⟨θ, hθ⟩

private theorem rung_aux
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A],
      GaloisRepAdic A → Prop}
    (hmono : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A]
      (ρ : GaloisRepAdic A), 𝒟₀ ρ → 𝒟' ρ)
    (D₀ : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟₀)
    (D' : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟')
    {T : Type} [CommRing T] [IsLocalRing T] [Algebra 𝒪 T]
    [Module.Finite 𝒪 T] [Module.Free 𝒪 T]
    (φ₀ : D₀.R →ₐ[𝒪] T) (hφ₀ : Function.Bijective φ₀)
    (hCIT : ∃ (n : ℕ) (f : Fin n → MvPowerSeries (Fin n) 𝒪),
      Nonempty ((MvPowerSeries (Fin n) 𝒪 ⧸ Ideal.span (Set.range f)) ≃ₐ[𝒪] T))
    (πT : T →ₐ[𝒪] 𝒪) (hη : (RingHom.ker πT).annihilator.map πT ≠ ⊥)
    (x₀ : D₀.R →ₐ[𝒪] 𝒪) (hx₀ : πT.comp φ₀ = x₀)
    (M : Type) [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    [Module.Finite 𝒪 M] [Module.Free 𝒪 M] [Module.Free T M]
    (B : M →ₗ[𝒪] M →ₗ[𝒪] 𝒪) (hB : ∀ (t : T) (m n : M), B (t • m) n = B m (t • n))
    (hBb : Function.Bijective B)
    {T' : Type} [CommRing T'] [IsLocalRing T'] [Algebra 𝒪 T']
    [Module.Finite 𝒪 T'] [Module.Free 𝒪 T']
    (ρ' : GaloisRepAdic T')
    (hsurj' : ∃ ψ : D'.R →ₐ[𝒪] T', Function.Surjective ψ ∧
      ∃ hψ : IsLocalHom (ψ : D'.R →+* T'),
        (D'.ρ.baseChangeAlong (ψ : D'.R →+* T') hψ).IsEquiv ρ')
    (πT' : T' →ₐ[𝒪] 𝒪) (hη' : (RingHom.ker πT').annihilator.map πT' ≠ ⊥)
    (M' : Type) [AddCommGroup M'] [Module T' M'] [Module 𝒪 M'] [IsScalarTower 𝒪 T' M']
    [Module.Finite 𝒪 M'] [Module.Free 𝒪 M']
    (B' : M' →ₗ[𝒪] M' →ₗ[𝒪] 𝒪) (hB' : ∀ (t : T') (m n : M'), B' (t • m) n = B' m (t • n))
    (hBb' : Function.Bijective B')
    (hM' : Submodule.torsionBySet T' M' ↑(RingHom.ker πT') ≠ ⊥)
    (hrank' : Module.finrank 𝒪 M' =
      Module.finrank 𝒪 (Submodule.torsionBySet T' M' ↑(RingHom.ker πT')) * Module.finrank 𝒪 T')
    (c : 𝒪) (hc : c ≠ 0)
    (hW8 : ∃ (i : M →ₗ[𝒪] M') (j : M' →ₗ[𝒪] M) (Δ : T),
      (∀ (m' : M') (m : M), B (j m') m = B' m' (i m)) ∧
      (∀ m : M, j (i m) = Δ • m) ∧
      Ideal.span {πT Δ} = Ideal.span {c} ∧
      (Submodule.map i ((Submodule.torsionBySet T M ↑(RingHom.ker πT)).restrictScalars 𝒪) =
        (Submodule.torsionBySet T' M' ↑(RingHom.ker πT')).restrictScalars 𝒪))
    (hcot : ∀ (θ : D'.R →ₐ[𝒪] D₀.R) (hθ : IsLocalHom (θ : D'.R →+* D₀.R)),
      (D'.ρ.baseChangeAlong (θ : D'.R →+* D₀.R) hθ).IsEquiv D₀.ρ →
      Module.length 𝒪 (RingHom.ker (x₀.comp θ)).Cotangent ≤
        Module.length 𝒪 (RingHom.ker x₀).Cotangent + Module.length 𝒪 (𝒪 ⧸ Ideal.span {c}))
    (hWPT : ∀ (φ' : D'.R →ₐ[𝒪] T') (hφ' : IsLocalHom (φ' : D'.R →+* T')),
      (D'.ρ.baseChangeAlong (φ' : D'.R →+* T') hφ').IsEquiv ρ' →
      ∀ (θ : D'.R →ₐ[𝒪] D₀.R) (hθ : IsLocalHom (θ : D'.R →+* D₀.R)),
      (D'.ρ.baseChangeAlong (θ : D'.R →+* D₀.R) hθ).IsEquiv D₀.ρ →
      πT'.comp φ' = x₀.comp θ) :
    ∃ φ' : D'.R →ₐ[𝒪] T', ∃ hφ' : IsLocalHom (φ' : D'.R →+* T'),
      (D'.ρ.baseChangeAlong (φ' : D'.R →+* T') hφ').IsEquiv ρ' ∧
      Function.Bijective φ' ∧
      (∃ (n : ℕ) (f : Fin n → MvPowerSeries (Fin n) 𝒪),
        Nonempty ((MvPowerSeries (Fin n) 𝒪 ⧸ Ideal.span (Set.range f)) ≃ₐ[𝒪] T')) ∧
      Module.Free T' M' := by

  obtain ⟨φ', hφ'surj, hφ'loc, hφ'equiv⟩ := hsurj'

  obtain ⟨θ, hθloc, hθequiv⟩ := levelLoweringMap_aux hmono D₀ D'

  have hπ' : πT'.comp φ' = x₀.comp θ := hWPT φ' hφ'loc hφ'equiv θ hθloc hθequiv

  have hS : (Module.finrank 𝒪 (Submodule.torsionBySet T M ↑(RingHom.ker πT)) : ℕ∞) *
      Module.length 𝒪 (RingHom.ker x₀).Cotangent ≤
      Module.length 𝒪 (M ⧸ (Submodule.torsionBySet T M ↑(RingHom.ker πT) ⊔
        Submodule.torsionBySet T M ↑(RingHom.ker πT).annihilator)) :=
    le_of_eq (AlgHom.length_cotangent_mul_eq_length_quotient_of_free
      φ₀ hφ₀ x₀ πT hx₀ hη hCIT M)

  obtain ⟨i, j, Δ, hadj, hji, hspan, h℘⟩ := hW8

  have hΔ : πT Δ ≠ 0 := by
    intro h0
    apply hc
    rw [← Ideal.span_singleton_eq_bot, ← hspan, h0, Ideal.span_singleton_eq_bot]

  have hcot' : Module.length 𝒪 (RingHom.ker (x₀.comp θ)).Cotangent ≤
      Module.length 𝒪 (RingHom.ker x₀).Cotangent +
        Module.length 𝒪 (𝒪 ⧸ Ideal.span {πT Δ}) := by
    rw [hspan]; exact hcot θ hθloc hθequiv

  obtain ⟨hbij, hCI', hfree'⟩ :=
    AlgHom.bijective_and_free_of_length_le_of_levelChange
      πT hη M B hB hBb x₀ hS φ' hφ'surj (x₀.comp θ) πT' hπ' hη' M' B' hB' hBb' hM' hrank'
      i j hadj Δ hji hΔ h℘ hcot'
  exact ⟨φ', hφ'loc, hφ'equiv, hbij, hCI', hfree'⟩

private theorem dock_aux
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (ℓ : ℕ) {R : Type} [CommRing R] [Algebra 𝒪 R]
    {T : Type} [CommRing T] [Nontrivial T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [Module.Free 𝒪 T]
    (φ : R →ₐ[𝒪] T) (hφ : Function.Bijective φ)
    (hCI : ∃ (n : ℕ) (f : Fin n → MvPowerSeries (Fin n) 𝒪),
      Nonempty ((MvPowerSeries (Fin n) 𝒪 ⧸ Ideal.span (Set.range f)) ≃ₐ[𝒪] T)) :
    ∃ (M : Type) (_ : AddCommGroup M) (_ : Module R M) (_ : Module T M) (_ : Nontrivial M),
      (∀ (x : R) (m : M), φ x • m = x • m) ∧
      ∃ r : ℕ, Nonempty (Algebra.PatchingDatum 𝒪 ℓ r R M) := by
  obtain ⟨n, f, ⟨e⟩⟩ := hCI
  let ψ : R ≃ₐ[𝒪] T := AlgEquiv.ofBijective φ hφ
  haveI : Module.Finite 𝒪 R := Module.Finite.equiv ψ.symm.toLinearEquiv
  haveI : Module.Free 𝒪 R := Module.Free.of_equiv ψ.symm.toLinearEquiv
  have hCI' : ∃ g : Fin n → MvPowerSeries (Fin n) 𝒪,
      Nonempty ((MvPowerSeries (Fin n) 𝒪 ⧸ Ideal.span (Set.range g)) ≃ₐ[𝒪] R) :=
    ⟨f, ⟨e.trans ψ.symm⟩⟩
  letI instRT : Module R T := Module.compHom T (φ : R →+* T)
  let η : R ≃ₗ[R] T :=
    { ψ.toEquiv with
      map_add' := fun x y => map_add φ x y
      map_smul' := fun x y => map_mul φ x y }
  haveI : Module.Free R T := Module.Free.of_equiv η
  haveI : Module.Finite R T := Module.Finite.equiv η
  obtain ⟨P⟩ := Algebra.PatchingDatum.nonempty_of_exists_presentation_of_free ℓ hCI' T
  exact ⟨T, inferInstance, instRT, inferInstance, inferInstance, fun _ _ => rfl, n, ⟨P⟩⟩

private theorem bijective_of_bijective_of_surjective_aux
    {𝒪 : Type} [CommRing 𝒪] {R T : Type} [CommRing R] [Algebra 𝒪 R] [CommRing T] [Algebra 𝒪 T]
    [Module.Finite 𝒪 T]
    (φ₁ : R →ₐ[𝒪] T) (hφ₁ : Function.Bijective φ₁)
    (φ₂ : R →ₐ[𝒪] T) (hφ₂ : Function.Surjective φ₂) :
    Function.Bijective φ₂ :=
  OrzechProperty.bijective_of_surjective_of_injective φ₁.toLinearMap φ₂.toLinearMap hφ₁.1 hφ₂

private theorem residue_comp_surjective_aux
    {𝒪 R T : Type} [CommRing 𝒪] [CommRing R] [IsLocalRing R] [CommRing T] [IsLocalRing T]
    [Algebra 𝒪 R] [Algebra 𝒪 T]
    (hR : Function.Surjective (IsLocalRing.residue R ∘ algebraMap 𝒪 R))
    (ψ : R →ₐ[𝒪] T) (hψs : Function.Surjective ψ) (hψ : IsLocalHom (ψ : R →+* T)) :
    Function.Surjective (IsLocalRing.residue T ∘ algebraMap 𝒪 T) := by
  intro t
  obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective t
  obtain ⟨r, rfl⟩ := hψs t
  obtain ⟨o, ho⟩ := hR (IsLocalRing.residue R r)
  refine ⟨o, ?_⟩
  simp only [Function.comp_apply] at ho ⊢
  rw [← ψ.commutes o]
  have hmem : algebraMap 𝒪 R o - r ∈ IsLocalRing.maximalIdeal R := Ideal.Quotient.eq.mp ho
  refine Ideal.Quotient.eq.mpr ?_
  rw [← map_sub]
  exact (IsLocalRing.mem_maximalIdeal _).mpr
    (map_nonunit (ψ : R →+* T) _ ((IsLocalRing.mem_maximalIdeal _).mp hmem))

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    (p : ℕ) (hp𝒪 : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    (ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪))

    (n : ℕ)
    (𝒟 : ℕ → ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop)
    (hmono : ∀ k, k < n → ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A]
      (ρ : GaloisRepAdic A), 𝒟 (k + 1) ρ → 𝒟 k ρ)

    (T : ℕ → Type) [∀ k, CommRing (T k)] [∀ k, IsLocalRing (T k)] [∀ k, IsNoetherianRing (T k)]
    [∀ k, IsAdicComplete (IsLocalRing.maximalIdeal (T k)) (T k)] [∀ k, Algebra 𝒪 (T k)]
    [∀ k, IsLocalHom (algebraMap 𝒪 (T k))] [∀ k, Module.Finite 𝒪 (T k)] [∀ k, Module.Free 𝒪 (T k)]
    (ρT : ∀ k, GaloisRepAdic (T k))
    (πT : ∀ k, T k →ₐ[𝒪] 𝒪)
    (hη : ∀ k, k ≤ n → (RingHom.ker (πT k)).annihilator.map (πT k) ≠ ⊥)
    (M : ℕ → Type) [∀ k, AddCommGroup (M k)] [∀ k, Module (T k) (M k)] [∀ k, Module 𝒪 (M k)]
    [∀ k, IsScalarTower 𝒪 (T k) (M k)] [∀ k, Module.Finite 𝒪 (M k)] [∀ k, Module.Free 𝒪 (M k)]
    (B : ∀ k, M k →ₗ[𝒪] M k →ₗ[𝒪] 𝒪)
    (hB : ∀ k, k ≤ n → ∀ (t : T k) (m m' : M k), B k (t • m) m' = B k m (t • m'))
    (hBb : ∀ k, k ≤ n → Function.Bijective (B k))
    (hM : ∀ k, k ≤ n → Submodule.torsionBySet (T k) (M k) ↑(RingHom.ker (πT k)) ≠ ⊥)
    (hrank : ∀ k, k ≤ n → Module.finrank 𝒪 (M k) =
      Module.finrank 𝒪 (Submodule.torsionBySet (T k) (M k) ↑(RingHom.ker (πT k))) *
        Module.finrank 𝒪 (T k))

    (hsurjn : ∀ D : GaloisRep.DeformationRingData 𝒪 ρbar (𝒟 n),
      ∃ ψ : D.R →ₐ[𝒪] T n, Function.Surjective ψ ∧ ∃ hψ : IsLocalHom (ψ : D.R →+* T n),
        (D.ρ.baseChangeAlong (ψ : D.R →+* T n) hψ).IsEquiv (ρT n))
    (hTW : ∀ (D : GaloisRep.DeformationRingData 𝒪 ρbar (𝒟 n))
      (φ : D.R →ₐ[𝒪] T n) (hφ : IsLocalHom (φ : D.R →+* T n)),
      (D.ρ.baseChangeAlong (φ : D.R →+* T n) hφ).IsEquiv (ρT n) →
      ∃ r : ℕ, Nonempty (@Algebra.PatchingDatum 𝒪 _ p r D.R _ _ (M n) _
        (Module.compHom (M n) (φ : D.R →+* T n))))

    (hrung : ∀ k, k < n →
      Nonempty (GaloisRep.DeformationRingData 𝒪 ρbar (𝒟 (k + 1))) ∧
      (∀ D' : GaloisRep.DeformationRingData 𝒪 ρbar (𝒟 k),
        ∃ ψ : D'.R →ₐ[𝒪] T k, Function.Surjective ψ ∧ ∃ hψ : IsLocalHom (ψ : D'.R →+* T k),
          (D'.ρ.baseChangeAlong (ψ : D'.R →+* T k) hψ).IsEquiv (ρT k)) ∧
      ∃ c : 𝒪, c ≠ 0 ∧
        (∃ (i : M (k + 1) →ₗ[𝒪] M k) (j : M k →ₗ[𝒪] M (k + 1)) (Δ : T (k + 1)),
          (∀ (m' : M k) (m : M (k + 1)), B (k + 1) (j m') m = B k m' (i m)) ∧
          (∀ m : M (k + 1), j (i m) = Δ • m) ∧
          Ideal.span {πT (k + 1) Δ} = Ideal.span {c} ∧
          Submodule.map i ((Submodule.torsionBySet (T (k + 1)) (M (k + 1))
              ↑(RingHom.ker (πT (k + 1)))).restrictScalars 𝒪) =
            (Submodule.torsionBySet (T k) (M k) ↑(RingHom.ker (πT k))).restrictScalars 𝒪) ∧
        ∀ (D₀ : GaloisRep.DeformationRingData 𝒪 ρbar (𝒟 (k + 1)))
          (D' : GaloisRep.DeformationRingData 𝒪 ρbar (𝒟 k))
          (φ₀ : D₀.R →ₐ[𝒪] T (k + 1)) (hφ₀ : IsLocalHom (φ₀ : D₀.R →+* T (k + 1))),
          (D₀.ρ.baseChangeAlong (φ₀ : D₀.R →+* T (k + 1)) hφ₀).IsEquiv (ρT (k + 1)) →
          (∀ (θ : D'.R →ₐ[𝒪] D₀.R) (hθ : IsLocalHom (θ : D'.R →+* D₀.R)),
            (D'.ρ.baseChangeAlong (θ : D'.R →+* D₀.R) hθ).IsEquiv D₀.ρ →
            Module.length 𝒪 (RingHom.ker (((πT (k + 1)).comp φ₀).comp θ)).Cotangent ≤
              Module.length 𝒪 (RingHom.ker ((πT (k + 1)).comp φ₀)).Cotangent +
                Module.length 𝒪 (𝒪 ⧸ Ideal.span {c})) ∧
          (∀ (φ' : D'.R →ₐ[𝒪] T k) (hφ' : IsLocalHom (φ' : D'.R →+* T k)),
            (D'.ρ.baseChangeAlong (φ' : D'.R →+* T k) hφ').IsEquiv (ρT k) →
            ∀ (θ : D'.R →ₐ[𝒪] D₀.R) (hθ : IsLocalHom (θ : D'.R →+* D₀.R)),
            (D'.ρ.baseChangeAlong (θ : D'.R →+* D₀.R) hθ).IsEquiv D₀.ρ →
            (πT k).comp φ' = ((πT (k + 1)).comp φ₀).comp θ)) :
    ∀ (D : GaloisRep.DeformationRingData 𝒪 ρbar (𝒟 0)) (ρ' : GaloisRepAdic (T 0)),
      𝒟 0 ρ' →
      ρ'.residual.IsEquiv
        (ρbar.baseChangeAlong (IsLocalRing.ResidueField.map (algebraMap 𝒪 (T 0)))) →
      (∃ ψ : D.R →ₐ[𝒪] T 0, Function.Surjective ψ ∧ ∃ hψ : IsLocalHom (ψ : D.R →+* T 0),
        (D.ρ.baseChangeAlong (ψ : D.R →+* T 0) hψ).IsEquiv ρ') →
      ∀ (φ : D.R →ₐ[𝒪] T 0) (hφ : IsLocalHom (φ : D.R →+* T 0)),
        (D.ρ.baseChangeAlong (φ : D.R →+* T 0) hφ).IsEquiv ρ' →
        ∃ (Mx : Type) (_ : AddCommGroup Mx) (_ : Module D.R Mx) (_ : Module (T 0) Mx)
          (_ : Nontrivial Mx),
          (∀ (x : D.R) (m : Mx), φ x • m = x • m) ∧
          ∃ r : ℕ, Nonempty (Algebra.PatchingDatum 𝒪 p r D.R Mx) := by
  classical
  intro D ρ' h𝒟' hres' hsurj' φ hφ hφe

  have key : ∀ k, k ≤ n → ∀ Dk : GaloisRep.DeformationRingData 𝒪 ρbar (𝒟 k),
      ∃ φk : Dk.R →ₐ[𝒪] T k, ∃ hφk : IsLocalHom (φk : Dk.R →+* T k),
        (Dk.ρ.baseChangeAlong (φk : Dk.R →+* T k) hφk).IsEquiv (ρT k) ∧
        Function.Bijective φk ∧
        (∃ (m : ℕ) (f : Fin m → MvPowerSeries (Fin m) 𝒪),
          Nonempty ((MvPowerSeries (Fin m) 𝒪 ⧸ Ideal.span (Set.range f)) ≃ₐ[𝒪] T k)) ∧
        Module.Free (T k) (M k) := by
    intro k hk
    refine Nat.decreasingInduction (n := n)
      (motive := fun k _ => ∀ Dk : GaloisRep.DeformationRingData 𝒪 ρbar (𝒟 k),
        ∃ φk : Dk.R →ₐ[𝒪] T k, ∃ hφk : IsLocalHom (φk : Dk.R →+* T k),
          (Dk.ρ.baseChangeAlong (φk : Dk.R →+* T k) hφk).IsEquiv (ρT k) ∧
          Function.Bijective φk ∧
          (∃ (m : ℕ) (f : Fin m → MvPowerSeries (Fin m) 𝒪),
            Nonempty ((MvPowerSeries (Fin m) 𝒪 ⧸ Ideal.span (Set.range f)) ≃ₐ[𝒪] T k)) ∧
          Module.Free (T k) (M k)) ?_ ?_ hk
    ·
      intro k hkn IH D'
      obtain ⟨⟨D₀⟩, hsurjk, c, hc, hW8, hwalls⟩ := hrung k hkn
      obtain ⟨φ₀, hφ₀l, e₀, hbij₀, hCI₀, hfree₀⟩ := IH D₀
      haveI : Module.Free (T (k + 1)) (M (k + 1)) := hfree₀
      obtain ⟨hcot, hWPT⟩ := hwalls D₀ D' φ₀ hφ₀l e₀
      obtain ⟨φ', hφ'l, e', hbij', hCI', hfree'⟩ :=
        rung_aux (hmono k hkn) D₀ D' φ₀ hbij₀ hCI₀ (πT (k + 1)) (hη (k + 1) hkn)
          ((πT (k + 1)).comp φ₀) rfl (M (k + 1)) (B (k + 1)) (hB (k + 1) hkn) (hBb (k + 1) hkn)
          (ρT k) (hsurjk D') (πT k) (hη k (le_of_lt hkn)) (M k) (B k) (hB k (le_of_lt hkn))
          (hBb k (le_of_lt hkn)) (hM k (le_of_lt hkn)) (hrank k (le_of_lt hkn)) c hc hW8 hcot hWPT
      exact ⟨φ', hφ'l, e', hbij', hCI', hfree'⟩
    ·
      intro Dn
      obtain ⟨ψ, hψs, hψl, eψ⟩ := hsurjn Dn
      obtain ⟨r, ⟨P⟩⟩ := hTW Dn ψ hψl eψ
      letI : Module Dn.R (M n) := Module.compHom (M n) (ψ : Dn.R →+* T n)
      haveI : Nontrivial (M n) := by
        by_contra htriv
        rw [not_nontrivial_iff_subsingleton] at htriv
        exact hM n le_rfl (Subsingleton.elim _ _)
      obtain ⟨hbij, -, hfreeT, -, f, hf⟩ :=
        P.bijective_and_free_of_surjective hp𝒪 ψ hψs (fun _ _ => rfl)
      exact ⟨ψ, hψl, eψ, hbij, ⟨r, f, hf⟩, hfreeT⟩

  obtain ⟨φ₁, -, -, hbij₁, hCI₀, -⟩ := key 0 (Nat.zero_le n) D
  obtain ⟨ψ, hψs, hψl, eψ⟩ := hsurj'
  have hT₀ : Function.Surjective (IsLocalRing.residue (T 0) ∘ algebraMap 𝒪 (T 0)) :=
    residue_comp_surjective_aux D.residue_surjective ψ hψs hψl
  obtain rfl : φ = ψ :=
    (D.universal (T 0) hT₀ ρ' h𝒟' hres').unique ⟨hφ, hφe⟩ ⟨hψl, eψ⟩
  have hbij : Function.Bijective φ := bijective_of_bijective_of_surjective_aux φ₁ hbij₁ φ hψs
  exact dock_aux p φ hbij hCI₀

#print axioms solution

end S_GaloisRep_DeformationRingData_exists_patchingDatum_of_ladder
end P2MW
export P2MW.S_GaloisRep_DeformationRingData_exists_patchingDatum_of_ladder (solution)
