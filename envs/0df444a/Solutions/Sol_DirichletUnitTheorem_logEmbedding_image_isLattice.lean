-- Prove2me | solution 1 for DirichletUnitTheorem.logEmbedding_image_isLattice
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T02:23:04.789895+00:00
-- url     : https://prove2.me/submissions/e817a16e-09ea-4f2e-9f99-a629fcde6353

import Mathlib
open NumberField

open NumberField.Units NumberField.Units.dirichletUnitTheorem in
theorem solution (K : Type*) [Field K] [NumberField K] :
    DiscreteTopology (Set.range fun (u : (𝓞 K)ˣ) (w : InfinitePlace K) =>
        (w.mult : ℝ) * Real.log (w ((u : 𝓞 K) : K))) ∧
      (Submodule.span ℝ (Set.range fun (u : (𝓞 K)ˣ) (w : InfinitePlace K) =>
          (w.mult : ℝ) * Real.log (w ((u : 𝓞 K) : K))) : Set (InfinitePlace K → ℝ)) =
        {x | ∑ w, x w = 0} := by
  classical
  set F : (𝓞 K)ˣ → InfinitePlace K → ℝ := fun u w =>
    (w.mult : ℝ) * Real.log (w ((u : 𝓞 K) : K)) with hF
  -- restriction to the places different from `w₀`
  let R : (InfinitePlace K → ℝ) →ₗ[ℝ] logSpace K :=
    LinearMap.funLeft ℝ ℝ (Subtype.val : {w : InfinitePlace K // w ≠ w₀} → InfinitePlace K)
  have hR : ∀ x, R x = fun w => x w.val := fun x => rfl
  have hRF : ∀ u, R (F u) = logEmbedding K (Additive.ofMul u) := fun u => rfl
  have hsumF : ∀ u, ∑ w, F u w = 0 := fun u => Units.sum_mult_mul_log u
  -- `R` is injective on the hyperplane `∑ x w = 0`
  have hinj : ∀ x y : InfinitePlace K → ℝ, ∑ w, x w = 0 → ∑ w, y w = 0 → R x = R y → x = y := by
    intro x y hx hy hxy
    have hc : ∀ w : {w : InfinitePlace K // w ≠ w₀}, x w = y w := fun w => congrFun hxy w
    funext w
    by_cases hw : w = w₀
    · subst hw
      rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀] at hx hy
      have : ∑ w : {w : InfinitePlace K // w ≠ w₀}, x w = ∑ w : {w : InfinitePlace K // w ≠ w₀}, y w :=
        Finset.sum_congr rfl fun w _ => hc w
      linarith
    · exact hc ⟨w, hw⟩
  refine ⟨?_, ?_⟩
  · -- discreteness
    let g : Set.range F → unitLattice K := fun x => ⟨R x.1, by
      obtain ⟨u, hu⟩ := x.2
      rw [← hu, hRF]
      exact ⟨Additive.ofMul u, Submodule.mem_top, rfl⟩⟩
    refine DiscreteTopology.of_continuous_injective (f := g) ?_ ?_
    · exact Continuous.subtype_mk ((LinearMap.continuous_of_finiteDimensional R).comp
        continuous_subtype_val) _
    · rintro ⟨_, ⟨u, rfl⟩⟩ ⟨_, ⟨v, rfl⟩⟩ h
      exact Subtype.ext (hinj _ _ (hsumF u) (hsumF v) (congrArg Subtype.val h))
  · -- span
    let H : Submodule ℝ (InfinitePlace K → ℝ) := LinearMap.ker
      (∑ w : InfinitePlace K, LinearMap.proj (R := ℝ) (φ := fun _ : InfinitePlace K => ℝ) w)
    have hH : ∀ x, x ∈ H ↔ ∑ w, x w = 0 := by
      intro x; simp [H]
    ext x
    simp only [SetLike.mem_coe, Set.mem_ofPred_eq]
    constructor
    · intro hx
      have : Submodule.span ℝ (Set.range F) ≤ H := by
        rw [Submodule.span_le]
        rintro _ ⟨u, rfl⟩
        exact (hH _).mpr (hsumF u)
      exact (hH x).mp (this hx)
    · intro hx
      have himg : R '' Set.range F = (unitLattice K : Set (logSpace K)) := by
        ext y
        simp only [Set.mem_image, Set.mem_range, SetLike.mem_coe]
        constructor
        · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
          rw [hRF]
          exact ⟨Additive.ofMul u, Submodule.mem_top, rfl⟩
        · rintro ⟨u, -, rfl⟩
          exact ⟨F u.toMul, ⟨u.toMul, rfl⟩, hRF _⟩
      have hspan : Submodule.map R (Submodule.span ℝ (Set.range F)) = ⊤ := by
        rw [Submodule.map_span, himg, unitLattice_span_eq_top]
      have : R x ∈ Submodule.map R (Submodule.span ℝ (Set.range F)) := by
        rw [hspan]; exact Submodule.mem_top
      obtain ⟨y, hy, hyx⟩ := this
      have hyH : ∑ w, y w = 0 := by
        have : Submodule.span ℝ (Set.range F) ≤ H := by
          rw [Submodule.span_le]
          rintro _ ⟨u, rfl⟩
          exact (hH _).mpr (hsumF u)
        exact (hH y).mp (this hy)
      rw [← hinj y x hyH hx hyx]
      exact hy
