-- Prove2me | solution 1 for ConsistentSubmodular.Checkpoints.exists_subset_fraction
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:38:39.716121+00:00
-- url     : https://prove2.me/submissions/8acbe4b8-a3e2-4fbe-a285-24928188c97a

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements
import Theorems.Thm_ConsistentSubmodular_Checkpoints_exists_subset_ratio

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Checkpoints
variable {n : ℕ}

theorem solution (f : Objective n) {A : Finset (Fin n)} {κ k : ℕ}
    (hA : A.card ≤ k) (hκ : κ ≤ k) (hk : 0 < k) :
    ∃ T ⊆ A, T.card ≤ κ ∧ (κ : ℝ) / k * f.value A ≤ f.value T := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hfA := f.nonnegative A
  rcases le_or_gt A.card κ with hAκ | hAκ
  · refine ⟨A, Finset.Subset.refl A, hAκ, ?_⟩
    have : (κ : ℝ) / k ≤ 1 := (div_le_one hkR).mpr (by exact_mod_cast hκ)
    nlinarith
  · obtain ⟨T, hT, hTcard, hTval⟩ := exists_subset_ratio f A.card A rfl κ hAκ.le
    refine ⟨T, hT, hTcard.le, ?_⟩
    have hm : (0 : ℝ) < A.card := by exact_mod_cast (show 0 < A.card by omega)
    have hmk : (A.card : ℝ) ≤ k := by exact_mod_cast hA
    have hfT := f.nonnegative T
    rw [div_mul_eq_mul_div, div_le_iff₀ hkR]
    nlinarith

end
