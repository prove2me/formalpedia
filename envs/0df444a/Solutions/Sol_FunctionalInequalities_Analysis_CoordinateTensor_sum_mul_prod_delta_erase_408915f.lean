-- Prove2me | solution 1 for FunctionalInequalities.Analysis.CoordinateTensor.sum_mul_prod_delta_erase_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:52:33.059449+00:00
-- url     : https://prove2.me/submissions/716dce61-ddce-4874-a1b9-a17bb1bbc0c2

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_EnergyForm
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_SlotAction
import Mathlib

noncomputable section
open Matrix
open scoped RealInnerProductSpace
section S3Bf2EnergyFormFirstOrder
open Matrix
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.CoordinateTensor
end FunctionalInequalities.Analysis.CoordinateTensor
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.CoordinateTensor
variable {n r : ℕ}
namespace FunctionalInequalities.Analysis.CoordinateTensor
end FunctionalInequalities.Analysis.CoordinateTensor
open FunctionalInequalities.Analysis.CoordinateTensor in
/-- **Delta collapse on all slots but one**: `Σ_{J'} f(J') Π_{s' ≠ s} δ_{J_{s'} J'_{s'}} = Σ_k f(J[s ↦ k])`. -/
theorem solution (J : Fin r → Fin n) (s : Fin r) (f : (Fin r → Fin n) → ℝ) :
    ∑ J' : Fin r → Fin n, f J' * ∏ s' ∈ Finset.univ.erase s, (if J s' = J' s' then (1 : ℝ) else 0) =
      ∑ k, f (Function.update J s k) := by
  classical
  let p : (Fin r → Fin n) → Prop :=
    fun J' => ∀ s' ∈ Finset.univ.erase s, J s' = J' s'
  have hprod (J' : Fin r → Fin n) :
      (∏ s' ∈ Finset.univ.erase s, (if J s' = J' s' then (1 : ℝ) else 0)) =
        if p J' then 1 else 0 := by
    by_cases hp : p J'
    · simp only [p, if_pos hp]
      apply Finset.prod_eq_one
      intro s' hs'
      exact if_pos (hp s' hs')
    · rw [if_neg hp]
      obtain ⟨s', hs', hne⟩ : ∃ s', s' ∈ Finset.univ.erase s ∧ J s' ≠ J' s' := by
        by_contra h
        apply hp
        intro s' hs'
        by_contra h'
        exact h ⟨s', hs', h'⟩
      exact Finset.prod_eq_zero hs' (if_neg hne)
  have hfilter :
      Finset.univ.filter p = Finset.univ.image (Function.update J s) := by
    ext J'
    constructor
    · intro hJ'
      have hp : p J' := (Finset.mem_filter.mp hJ').2
      have heq : Function.update J s (J' s) = J' := by
        funext s'
        by_cases hss' : s' = s
        · subst s'
          simp
        · have hmem : s' ∈ Finset.univ.erase s := by simp [hss']
          simp [Function.update, hss', hp s' hmem]
      exact Finset.mem_image.mpr ⟨J' s, Finset.mem_univ _, heq⟩
    · intro hJ'
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hJ'
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_univ _
      · intro s' hs'
        have hne : s' ≠ s := by simpa using hs'
        simp [Function.update, hne]
  calc
    ∑ J' : Fin r → Fin n, f J' *
        ∏ s' ∈ Finset.univ.erase s, (if J s' = J' s' then (1 : ℝ) else 0) =
        ∑ J', if p J' then f J' else 0 := by
      apply Finset.sum_congr rfl
      intro J' hJ'
      rw [hprod]
      by_cases hp : p J' <;> simp [hp]
    _ = ∑ J' ∈ Finset.univ.filter p, f J' := by
      rw [← Finset.sum_filter]
    _ = ∑ J' ∈ Finset.univ.image (Function.update J s), f J' := by
      rw [hfilter]
    _ = ∑ k, f (Function.update J s k) := by
      rw [Finset.sum_image]
      intro k hk l hl hkl
      exact (Function.update_injective J s) hkl
