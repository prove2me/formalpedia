-- Prove2me | solution 1 for DirichletUnitTheorem.regulator_well_defined
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T02:25:01.157394+00:00
-- url     : https://prove2.me/submissions/a808db9a-2b9b-438e-b4e9-7424d9e47b8b

import Mathlib
open NumberField

open NumberField.Units in
theorem regulator_well_defined_aux (K : Type*) [Field K] [NumberField K]
    [DecidableEq (InfinitePlace K)]
    (u : Fin (InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1) → (𝓞 K)ˣ)
    (hu : ∀ x : (𝓞 K)ˣ, ∃ ζ : (𝓞 K)ˣ, IsOfFinOrder ζ ∧ ∃ n : Fin _ → ℤ, x = ζ * ∏ i, u i ^ n i)
    (w₁ : InfinitePlace K)
    (e₁ : {w // w ≠ w₁} ≃ Fin (InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1)) :
    |(Matrix.of fun (i j : {w // w ≠ w₁}) =>
        ((j : InfinitePlace K).mult : ℝ) * Real.log ((j : InfinitePlace K) ((u (e₁ i) : 𝓞 K) : K))).det| =
      regulator K := by
  have h : rank K = InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1 := by
    rw [rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
  let u' : Fin (rank K) → (𝓞 K)ˣ := fun i => u (Fin.cast h i)
  have htop : Subgroup.closure (Set.range u') ⊔ torsion K = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨ζ, hζ, n, rfl⟩ := hu x
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_right ((CommGroup.mem_torsion _).mpr hζ))
      (Subgroup.prod_mem _ fun i _ => Subgroup.zpow_mem _ (Subgroup.mem_sup_left
        (Subgroup.subset_closure (Set.mem_range.mpr ⟨Fin.cast h.symm i, by simp [u']⟩))) _)
  have hreg : regOfFamily u' = regulator K := by
    have := regOfFamily_div_regulator u'
    rw [htop, Subgroup.index_top, Nat.cast_one, div_eq_one_iff_eq (regulator_ne_zero K)] at this
    exact this
  have key := regOfFamily_eq_det u' w₁ (e₁.trans (finCongr h.symm))
  rw [hreg] at key
  rw [key]
  congr! 3

theorem solution (K : Type*) [Field K] [NumberField K]
    [DecidableEq (InfinitePlace K)]
    (u v : Fin (InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1) → (𝓞 K)ˣ)
    (hu : ∀ x : (𝓞 K)ˣ, ∃ ζ : (𝓞 K)ˣ, IsOfFinOrder ζ ∧ ∃ n : Fin _ → ℤ, x = ζ * ∏ i, u i ^ n i)
    (hv : ∀ x : (𝓞 K)ˣ, ∃ ζ : (𝓞 K)ˣ, IsOfFinOrder ζ ∧ ∃ n : Fin _ → ℤ, x = ζ * ∏ i, v i ^ n i)
    (w₁ w₂ : InfinitePlace K)
    (e₁ : {w // w ≠ w₁} ≃ Fin (InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1))
    (e₂ : {w // w ≠ w₂} ≃ Fin (InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1)) :
    |(Matrix.of fun (i j : {w // w ≠ w₁}) =>
        ((j : InfinitePlace K).mult : ℝ) * Real.log ((j : InfinitePlace K) ((u (e₁ i) : 𝓞 K) : K))).det| =
      |(Matrix.of fun (i j : {w // w ≠ w₂}) =>
        ((j : InfinitePlace K).mult : ℝ) * Real.log ((j : InfinitePlace K) ((v (e₂ i) : 𝓞 K) : K))).det| ∧
    0 < |(Matrix.of fun (i j : {w // w ≠ w₁}) =>
        ((j : InfinitePlace K).mult : ℝ) * Real.log ((j : InfinitePlace K) ((u (e₁ i) : 𝓞 K) : K))).det| := by
  rw [regulator_well_defined_aux K u hu w₁ e₁, regulator_well_defined_aux K v hv w₂ e₂]
  exact ⟨rfl, Units.regulator_pos K⟩
