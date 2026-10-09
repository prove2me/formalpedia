-- Prove2me | solution 1 for DiazModulus.rank_one_config_card_le_finrank_add_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-08T16:53:07.369098+00:00
-- url     : https://prove2.me/submissions/e8d8cdc3-f2b8-4032-a7a2-e44ca1d9bbfd

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_polynomial_submodule_mul_finrank_ge

open Complex ComplexConjugate

/-!
# A rank-one configuration inside a space of rational functions

Let `u` be transcendental over `K` and `V₀ ⊆ K(u)` a finite-dimensional `K`-space containing all
products `x i * y j`, with `x₁, …, x_p` and `y₁, …, y_q` linearly independent. Then
`p + q ≤ dim V₀ + 1`.

The finitely many products `x i * y j` lie in `K(u)`, so they have a common denominator: a
polynomial `g` with `g(u) ≠ 0` and `g(u) x i y j = A i j (u)` for polynomials `A i j`
(`IntermediateField.mem_adjoin_simple_iff`, induction over a finset). Evaluation at `u` is
injective on `K[X]` (`transcendental_iff_injective`), so the minor identity
`A i 0 * A 0 j = A 0 0 * A i j` holds in `K[X]`. Put `P = span {A i 0}`, `Q = span {A 0 j}`,
`N = span {A i j}`. Then `dim P = p`, `dim Q = q` (evaluation sends these families to non-zero
multiples of `x` and `y`), `P * Q ⊆ A 0 0 · N`, and `v ↦ g(u)⁻¹ v(u)` embeds `N` into `V₀`.
`polynomial_submodule_mul_finrank_ge` gives `p + q ≤ dim (P * Q) + 1 ≤ dim N + 1 ≤ dim V₀ + 1`.
-/

namespace R6_rankOne

open Polynomial

/-- Finitely many elements of `K(u)` have a common denominator. -/
theorem common_denom {K : Subfield ℂ} (u : ℂ) (F : Finset ℂ)
    (hF : ∀ v ∈ F, v ∈ IntermediateField.adjoin K ({u} : Set ℂ)) :
    ∃ g : K[X], aeval u g ≠ 0 ∧ ∀ v ∈ F, ∃ r : K[X], aeval u r = aeval u g * v := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1, by simp, by simp⟩
  | insert a F _ ih =>
    obtain ⟨g, hg, hgF⟩ := ih (fun v hv => hF v (Finset.mem_insert_of_mem hv))
    obtain ⟨r, s, hrs⟩ :=
      (IntermediateField.mem_adjoin_simple_iff (F := K) (α := u) a).mp (hF a (Finset.mem_insert_self a F))
    by_cases hs : aeval u s = 0
    · refine ⟨g, hg, fun v hv => ?_⟩
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact ⟨0, by simp [hrs, hs]⟩
      · exact hgF v hv
    · refine ⟨g * s, by simp [hg, hs], fun v hv => ?_⟩
      rcases Finset.mem_insert.mp hv with rfl | hv
      · refine ⟨g * r, ?_⟩
        rw [hrs, map_mul, map_mul]
        field_simp
      · obtain ⟨r', hr'⟩ := hgF v hv
        exact ⟨r' * s, by rw [map_mul, map_mul, hr']; ring⟩

end R6_rankOne

open DiazModulus R6_rankOne in
theorem solution (K : Subfield ℂ) (u : ℂ)
    (hT : Transcendental K u) (V₀ : Submodule K ℂ) [FiniteDimensional K V₀]
    (hV₀ : ∀ v ∈ V₀, v ∈ IntermediateField.adjoin K ({u} : Set ℂ))
    (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (x : Fin p → ℂ) (y : Fin q → ℂ)
    (hx : LinearIndependent K x) (hy : LinearIndependent K y)
    (hxy : ∀ i j, x i * y j ∈ V₀) :
    p + q ≤ Module.finrank K V₀ + 1 := by
  classical
  have hinj : Function.Injective (Polynomial.aeval u : Polynomial K →ₐ[K] ℂ) :=
    transcendental_iff_injective.mp hT
  obtain ⟨g, hg, hgF⟩ := common_denom u
    (Finset.univ.image fun ij : Fin p × Fin q => x ij.1 * y ij.2)
    (by
      intro v hv
      obtain ⟨ij, -, rfl⟩ := Finset.mem_image.mp hv
      exact hV₀ _ (hxy ij.1 ij.2))
  have hA : ∀ i j, ∃ r : Polynomial K,
      Polynomial.aeval u r = Polynomial.aeval u g * (x i * y j) := fun i j =>
    hgF _ (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩)
  choose A hA using hA
  set c := Polynomial.aeval u g with hc
  let i0 : Fin p := ⟨0, hp⟩
  let j0 : Fin q := ⟨0, hq⟩
  have hx0 : x i0 ≠ 0 := hx.ne_zero i0
  have hy0 : y j0 ≠ 0 := hy.ne_zero j0
  have hmin : ∀ i j, A i j0 * A i0 j = A i0 j0 * A i j := fun i j =>
    hinj (by simp only [map_mul, hA]; ring)
  have hA00 : A i0 j0 ≠ 0 := by
    intro h
    have := hA i0 j0
    rw [h, map_zero] at this
    exact mul_ne_zero hg (mul_ne_zero hx0 hy0) this.symm
  -- the two families are linearly independent
  have hPli : LinearIndependent K (fun i => A i j0) := by
    apply LinearIndependent.of_comp (Polynomial.aeval u : Polynomial K →ₐ[K] ℂ).toLinearMap
    have heq : (Polynomial.aeval u : Polynomial K →ₐ[K] ℂ).toLinearMap ∘ (fun i => A i j0) =
        (LinearMap.mulLeft K (c * y j0)) ∘ x := by
      funext i; simp only [Function.comp_apply, AlgHom.toLinearMap_apply, hA,
        LinearMap.mulLeft_apply]; ring
    rw [heq]
    exact hx.map' _ (LinearMap.ker_eq_bot.mpr (mul_right_injective₀ (mul_ne_zero hg hy0)))
  have hQli : LinearIndependent K (fun j => A i0 j) := by
    apply LinearIndependent.of_comp (Polynomial.aeval u : Polynomial K →ₐ[K] ℂ).toLinearMap
    have heq : (Polynomial.aeval u : Polynomial K →ₐ[K] ℂ).toLinearMap ∘ (fun j => A i0 j) =
        (LinearMap.mulLeft K (c * x i0)) ∘ y := by
      funext j; simp only [Function.comp_apply, AlgHom.toLinearMap_apply, hA,
        LinearMap.mulLeft_apply]; ring
    rw [heq]
    exact hy.map' _ (LinearMap.ker_eq_bot.mpr (mul_right_injective₀ (mul_ne_zero hg hx0)))
  set P := Submodule.span K (Set.range fun i => A i j0) with hP
  set Q := Submodule.span K (Set.range fun j => A i0 j) with hQ
  set N := Submodule.span K (Set.range fun ij : Fin p × Fin q => A ij.1 ij.2) with hN
  have : FiniteDimensional K P := FiniteDimensional.span_of_finite K (Set.finite_range _)
  have : FiniteDimensional K Q := FiniteDimensional.span_of_finite K (Set.finite_range _)
  have : FiniteDimensional K N := FiniteDimensional.span_of_finite K (Set.finite_range _)
  have hPdim : Module.finrank K P = p := by
    rw [hP, finrank_span_eq_card hPli, Fintype.card_fin]
  have hQdim : Module.finrank K Q = q := by
    rw [hQ, finrank_span_eq_card hQli, Fintype.card_fin]
  have hPne : P ≠ ⊥ := by
    intro h; rw [h, finrank_bot] at hPdim; omega
  have hQne : Q ≠ ⊥ := by
    intro h; rw [h, finrank_bot] at hQdim; omega
  have key := DiazModulus.polynomial_submodule_mul_finrank_ge K P Q hPne hQne
  -- `P * Q ⊆ A₀₀ · N`
  set N' := N.map (LinearMap.mulLeft K (A i0 j0)) with hN'
  have : FiniteDimensional K N' := inferInstance
  have hle : P * Q ≤ N' := by
    rw [hP, hQ, Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    show A i j0 * A i0 j ∈ N'
    rw [hmin]
    exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨(i, j), rfl⟩)
  have h1 : Module.finrank K ↥(P * Q) ≤ Module.finrank K N' := Submodule.finrank_mono hle
  have h2 : Module.finrank K N' ≤ Module.finrank K N := Submodule.finrank_map_le _ _
  -- `N` embeds into `V₀`
  let L : Polynomial K →ₗ[K] ℂ :=
    (LinearMap.mulLeft K c⁻¹) ∘ₗ (Polynomial.aeval u : Polynomial K →ₐ[K] ℂ).toLinearMap
  have hLinj : Function.Injective L := by
    intro a b hab
    apply hinj
    simpa [L, LinearMap.mulLeft_apply, hg] using hab
  have hLN : ∀ n : N, L n ∈ V₀ := by
    have : N ≤ V₀.comap L := by
      rw [hN, Submodule.span_le]
      rintro _ ⟨ij, rfl⟩
      show L (A ij.1 ij.2) ∈ V₀
      simp only [L, LinearMap.comp_apply, AlgHom.toLinearMap_apply, hA,
        LinearMap.mulLeft_apply]
      rw [← mul_assoc, inv_mul_cancel₀ hg, one_mul]
      exact hxy _ _
    exact fun n => this n.2
  let f : N →ₗ[K] V₀ := (L.domRestrict N).codRestrict V₀ hLN
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply hLinj
    exact congrArg Subtype.val hab
  have h3 : Module.finrank K N ≤ Module.finrank K V₀ :=
    LinearMap.finrank_le_finrank_of_injective hf
  omega
