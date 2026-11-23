-- Prove2me | solution 1 for Formalism.CyclotomicNorms.AdaptiveSubstitution.exists_exps_adaptive
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:24.587799+00:00
-- url     : https://prove2.me/submissions/52524e7d-4683-4c01-88ac-81e01a3f02d3

import Definitions.Def_Formalism_CyclotomicNorms_DiscardKernel
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_SubstitutionBound
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_AdaptiveSubstitutionBound
import Theorems.Thm_Formalism_CyclotomicNorms_AdaptiveSubstitution_pre_eq
import Theorems.Thm_Formalism_CyclotomicNorms_AdaptiveSubstitution_mem_pre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.CyclotomicNorms
open Formalism.CyclotomicNorms.AdaptiveSubstitution
namespace Formalism.CyclotomicNorms.AdaptiveSubstitution
theorem _root_.solution (ℓ : ℕ) {r s : ℕ} (hℓ : 2 ≤ ℓ) (α : Fin s → Fin r →₀ ℕ)
    (B : List ℕ → ℕ) :
    ∃ e : Fin r → ℕ, StrictMono e ∧
      (∀ j : Fin r, B (List.ofFn fun i : Fin (j : ℕ) => e (Fin.castLE (Nat.le_of_lt j.isLt) i)) ≤ e j) ∧
      ∀ t j, ∑ i ∈ univ.filter (· < j), α t i * ℓ ^ e i < ℓ ^ e j := by
  set A : ℕ := ∑ t, ∑ i, α t i with hA
  have hαA : ∀ t, ∑ i, α t i ≤ A := fun t =>
    Finset.single_le_sum (f := fun t' => ∑ i', α t' i') (fun _ _ => Nat.zero_le _) (mem_univ t)
  have hℓpos : 0 < ℓ := by omega
  refine ⟨fun j => step ℓ A B (pre ℓ A B j), ?_, ?_, ?_⟩
  · intro a b hab
    have hab' : (a : ℕ) < b := hab
    have hm := mem_pre ℓ A B hab'
    have hle := List.le_sum_of_mem hm
    simp only [step] at hle ⊢
    omega
  · intro j
    have : (List.ofFn fun i : Fin (j : ℕ) =>
        step ℓ A B (pre ℓ A B (Fin.castLE (Nat.le_of_lt j.isLt) i : ℕ))) = pre ℓ A B j := by
      rw [pre_eq ℓ A B j]
      rfl
    simp only
    rw [this]
    simp only [step]
    omega
  · intro t j
    set S := ((pre ℓ A B j).map (ℓ ^ ·)).sum with hS
    have hterm : ∀ i ∈ univ.filter (· < j),
        α t i * ℓ ^ step ℓ A B (pre ℓ A B i) ≤ α t i * S := by
      intro i hi
      have hij : (i : ℕ) < j := by simpa using hi
      apply Nat.mul_le_mul_left
      exact List.le_sum_of_mem (List.mem_map_of_mem (mem_pre ℓ A B hij))
    have h1 : ∑ i ∈ univ.filter (· < j), α t i * ℓ ^ step ℓ A B (pre ℓ A B i) ≤ A * S := by
      calc ∑ i ∈ univ.filter (· < j), α t i * ℓ ^ step ℓ A B (pre ℓ A B i)
          ≤ ∑ i ∈ univ.filter (· < j), α t i * S := Finset.sum_le_sum hterm
        _ ≤ ∑ i, α t i * S :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => Nat.zero_le _)
        _ = (∑ i, α t i) * S := by rw [Finset.sum_mul]
        _ ≤ A * S := Nat.mul_le_mul_right _ (hαA t)
    have h2 : A * S < step ℓ A B (pre ℓ A B j) := by
      simp only [step, ← hS]
      omega
    have h3 : step ℓ A B (pre ℓ A B j) < ℓ ^ step ℓ A B (pre ℓ A B j) :=
      lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_left hℓ _)
    simp only
    omega
end Formalism.CyclotomicNorms.AdaptiveSubstitution
