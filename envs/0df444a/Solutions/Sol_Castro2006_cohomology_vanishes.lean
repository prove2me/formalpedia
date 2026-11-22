-- Prove2me | solution 1 for Castro2006.cohomology_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-22T15:58:01.761436+00:00
-- url     : https://prove2.me/submissions/0fddf764-3dca-4140-aa61-d2c3f5474c74

import Mathlib
open CategoryTheory

/-! Coprime vanishing of `Hⁿ(G, A)` (Castro 2006, Proposição 4.4.1(ii)).

`|G|` kills `Hⁿ(G, A)` for `n ≥ 1`: the map `A → Coind_1^G A → A`, `a ↦ (h ↦ h a) ↦ Σ h⁻¹ (h a)`,
is multiplication by `|G|`, and `Hⁿ(G, Coind_1^G A) ≅ Hⁿ(1, A) = 0` (Shapiro). When `|G|` is
invertible on `A` (coprime case), multiplication by `|G|` is an automorphism, so `Hⁿ(G, A) = 0`. -/

/-- If `|G|` acts invertibly on `A` (via `u`), then `Hⁿ⁺¹(G, A) = 0`. -/
theorem Castro2006_aux {k G : Type} [CommRing k] [Group G] [Fintype G] (A : Rep k G) (n : ℕ)
    (u : k) (hu : ∀ a : A.V, u • ((Fintype.card G : k) • a) = a) :
    Limits.IsZero (groupCohomology A (n + 1)) := by
  classical
  let S : Subgroup G := ⊥
  let B : Rep k S := Rep.res S.subtype A
  let C : Rep k G := Rep.coind S.subtype B
  have hC : Limits.IsZero (groupCohomology C (n + 1)) :=
    (isZero_groupCohomology_succ_of_subsingleton B n).of_iso (groupCohomology.coindIso B (n + 1))
  let ι : A ⟶ C := Rep.resCoindToHom S.subtype A B (𝟙 _)
  let τl : C.V →ₗ[k] A.V := ∑ h : G, A.ρ h⁻¹ ∘ₗ LinearMap.proj h ∘ₗ
    (Representation.coindV S.subtype B.ρ).subtype
  have hτl : ∀ c : C.V, τl c = ∑ h : G, A.ρ h⁻¹ (c.1 h) := by
    intro c
    simp [τl]
    rfl
  let τ : C ⟶ A := Rep.ofHom
    { toLinearMap := τl
      isIntertwining' := fun g => by
        ext c
        simp only [LinearMap.coe_comp, Function.comp_apply, hτl]
        rw [map_sum]
        refine (Fintype.sum_equiv (Equiv.mulRight g) _ _ fun h => ?_)
        simp [← Module.End.mul_apply, ← map_mul]
        rfl }
  have hφ : ∀ a : A.V, (ι ≫ τ).hom a = (Fintype.card G : k) • a := by
    intro a
    simp [ι, τ, hτl, ← Module.End.mul_apply, ← map_mul, Nat.cast_smul_eq_nsmul]
  let ψ : A ⟶ A := u • 𝟙 A
  have hψ : (ι ≫ τ) ≫ ψ = 𝟙 A := by
    ext a
    show ψ.hom ((ι ≫ τ).hom a) = a
    rw [hφ]
    simp [ψ, Rep.smul_hom]
    rw [smul_smul, mul_comm, ← smul_smul]
    exact hu a
  let F := groupCohomology.functor k G (n + 1)
  rw [Limits.IsZero.iff_id_eq_zero]
  have : 𝟙 (F.obj A) = F.map ι ≫ (F.map τ ≫ F.map ψ) := by
    rw [← F.map_comp, ← F.map_comp, ← Category.assoc, hψ, F.map_id]
  have hC' : Limits.IsZero (F.obj C) := hC
  exact this.trans (by rw [hC'.eq_zero_of_tgt (F.map ι), Limits.zero_comp]; rfl)

/-- Bézout: if `u g + v N = 1` and `N` kills `M`, then `u` inverts multiplication by `g`. -/
theorem Castro2006_unit {k M : Type} [CommRing k] [AddCommGroup M] [Module k M] (N g : ℕ)
    (hN : ∀ a : M, N • a = 0) (u v : k) (huv : u * g + v * N = 1) (a : M) :
    u • ((g : k) • a) = a := by
  have h1 : ((N : k)) • a = 0 := by
    rw [Nat.cast_smul_eq_nsmul]
    exact hN a
  calc u • ((g : k) • a) = (u * g + v * N) • a := by
        rw [add_smul, mul_smul, mul_smul, h1, smul_zero, add_zero]
    _ = a := by rw [huv, one_smul]

theorem solution {G : Type} [Group G] [Fintype G] (A : Rep ℤ G) [Fintype A] (n : ℕ)
    (hn : 1 ≤ n) (hcop : (Fintype.card G).Coprime (Fintype.card A)) :
    ∀ x : groupCohomology A n, x = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hc : IsCoprime (Fintype.card G : ℤ) (Fintype.card A : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr hcop
  obtain ⟨u, v, huv⟩ := hc
  -- `A.hV2` is passed explicitly: it is not defeq to `AddCommGroup.toIntModule`.
  have hZ := Castro2006_aux A m u (fun a =>
    @Castro2006_unit ℤ A.V _ _ A.hV2 (Fintype.card A) (Fintype.card G)
      (fun _ => card_nsmul_eq_zero) u v huv a)
  intro x
  exact (ModuleCat.subsingleton_of_isZero hZ).elim x 0
