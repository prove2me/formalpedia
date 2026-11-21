-- Prove2me | solution 1 for GRH.mobius_character_and_progression_bounds_above_record
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T00:35:37.596664+00:00
-- url     : https://prove2.me/submissions/a4a397a1-1b89-4afd-85ac-d5ab7e49a802

import Theorems.Thm_GRH_sharp_mobius_nonprincipal_above_record
import Theorems.Thm_GRH_principal_mobius_partial_sum_subpower
import Theorems.Thm_GRH_character_sum_bound_iff_reduced_residue_class_bounds

open Filter Asymptotics

theorem solution (q : ℕ) [NeZero q] (σ : ℝ) (hσ : (0.8749570698 : ℝ) < σ) :
    (∀ χ : DirichletCharacter ℂ q,
      (fun N : ℕ ↦ ∑ k ∈ Finset.range (N+1), χ k * (ArithmeticFunction.moebius k : ℂ)) =O[atTop]
        (fun N : ℕ ↦ (N : ℝ)^σ)) ∧
    (∀ a : ZMod q, IsUnit a →
      (fun N : ℕ ↦ ∑ k ∈ Finset.range (N+1), if a = (k : ZMod q) then
        (ArithmeticFunction.moebius k : ℂ) else 0) =O[atTop] (fun N : ℕ ↦ (N : ℝ)^σ)) := by
  have hχ (χ : DirichletCharacter ℂ q) :
      (fun N : ℕ ↦ ∑ k ∈ Finset.range (N+1), χ k * (ArithmeticFunction.moebius k : ℂ)) =O[atTop]
        (fun N : ℕ ↦ (N : ℝ)^σ) := by
    by_cases e : χ = 1
    · subst χ
      exact GRH.principal_mobius_partial_sum_subpower q σ hσ
    · exact GRH.sharp_mobius_nonprincipal_above_record q χ e σ hσ
  exact ⟨hχ, (GRH.character_sum_bound_iff_reduced_residue_class_bounds q
    (fun k ↦ (ArithmeticFunction.moebius k : ℂ)) (fun N : ℕ ↦ (N : ℝ)^σ)).mp hχ⟩
