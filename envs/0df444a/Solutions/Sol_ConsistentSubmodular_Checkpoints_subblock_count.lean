-- Prove2me | solution 1 for ConsistentSubmodular.Checkpoints.subblock_count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:33:50.084846+00:00
-- url     : https://prove2.me/submissions/8059cf45-d537-4327-b63f-450f7de18b3e

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_Reduction_CheckpointSchedule

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Checkpoints

variable {n : ℕ}

/-- Subblocks are disjoint and ordered. -/
theorem hi_le_lo (ℓ h : ℕ) {σ σ' : ℕ} (hσ : σ < σ') : hi ℓ h σ ≤ lo ℓ h σ' :=
  Nat.div_le_div_right (Nat.mul_le_mul_right ℓ hσ)

/-- At most one subblock contains a given update strictly inside its range. -/
theorem card_inside_le_one (ℓ h r : ℕ) :
    (Finset.univ.filter (fun σ : Fin h => lo ℓ h σ < r ∧ r < hi ℓ h σ)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  by_contra hab
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with hlt | hlt
  · have := hi_le_lo ℓ h hlt
    omega
  · have := hi_le_lo ℓ h hlt
    omega

end ConsistentSubmodular.Checkpoints

end

end

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Checkpoints
variable {n : ℕ} {α : ℝ}

theorem solution (ℓ h r : ℕ) (hh : 0 < h) :
    ((h : ℝ) - 1) / h ≤
      (∑ σ : Fin h, ((if r ≤ lo ℓ h σ then 1 else 0) +
        (if ¬ r ≤ lo ℓ h σ ∧ hi ℓ h σ ≤ r then 1 else 0) : ℝ)) / h := by
  have hpoint (σ : Fin h) : ((if r ≤ lo ℓ h σ then 1 else 0) +
      (if ¬ r ≤ lo ℓ h σ ∧ hi ℓ h σ ≤ r then 1 else 0) : ℝ) =
      1 - if lo ℓ h σ < r ∧ r < hi ℓ h σ then 1 else 0 := by
    by_cases h1 : r ≤ lo ℓ h σ
    · have : ¬ (lo ℓ h σ < r ∧ r < hi ℓ h σ) := fun h => by omega
      simp [h1, this]
    · by_cases h2 : hi ℓ h σ ≤ r
      · have : ¬ (lo ℓ h σ < r ∧ r < hi ℓ h σ) := fun h => by omega
        simp [h1, h2, this]
      · have : lo ℓ h σ < r ∧ r < hi ℓ h σ := ⟨by omega, by omega⟩
        simp [h1, h2, this]
  have hcount := card_inside_le_one ℓ h r
  have hsum : (∑ σ : Fin h, (if lo ℓ h σ < r ∧ r < hi ℓ h σ then 1 else 0 : ℝ)) ≤ 1 := by
    rw [Finset.sum_boole]
    exact_mod_cast hcount
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  apply div_le_div_of_nonneg_right _ hhR.le
  rw [Finset.sum_congr rfl fun σ _ => hpoint σ, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  linarith

end
