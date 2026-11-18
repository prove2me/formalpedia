-- Prove2me | solution 1 for CompDesignBFM.Supplement.theorem_C_1
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T05:08:50.47923+00:00
-- url     : https://prove2.me/submissions/cf941eab-d15d-451d-804d-71e85c79bfdb

import Mathlib
import Definitions.Def_CompDesignBFM_IsPriority
import Definitions.Def_CompDesignBFM_Amc
import Definitions.Def_CompDesignBFM_Supplement_IsBetaSelfBounding
import Definitions.Def_CompDesignBFM_Supplement_IsPNEOf
import Definitions.Def_CompDesignBFM_Supplement_scaledPay
import Theorems.Thm_CompDesignBFM_theorem_3_2

open CompDesignBFM CompDesignBFM.Supplement

theorem solution {n : ℕ} (v : Finset (Fin n) → ℝ) (B β : ℝ) (hB : 0 < B) (hβ : 0 < β)
    (hv0 : v ∅ = 0) (hv : IsBetaSelfBounding β v) (r : Finset (Fin n) → ℕ) (hr : IsPriority r)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) :
    IsPNEOf (scaledPay v B β) c (Amc v (B / β) r c) := by
  have hB' : 0 < B / β := div_pos hB hβ
  set S := Amc v (B / β) r c with hSdef
  have hmax : ∀ T, pot v (B / β) c T ≤ pot v (B / β) c S := fun T => Amc_isMax v (B / β) r c T
  have hpot0 : pot v (B / β) c ∅ = 0 := by simp [pot, hv0]
  have hS₀ : S = ∅ ∨ 0 < pot v (B / β) c S := by
    rcases (hpot0 ▸ hmax ∅ : (0 : ℝ) ≤ pot v (B / β) c S).lt_or_eq with h | h
    · exact Or.inr h
    · left
      have hall : ∀ U, pot v (B / β) c U ≤ pot v (B / β) c ∅ := by
        intro U
        have := hmax U
        rw [← h] at this
        rw [hpot0]; exact this
      have h1 : r S ≤ r ∅ := Amc_least v (B / β) r c ∅ hall
      have h2 : r ∅ ≤ r S := hr.2 S
      exact hr.1 (le_antisymm h1 h2)
  have hpne := CompDesignBFM.theorem_3_2 v (B / β) c hB' hv0 hv.2.1 hc S hmax hS₀
  have heq : ∀ T i, scaledPay v B β T i = mcPay v (B / β) T i := by
    intro T i
    unfold scaledPay mcPay
    split_ifs with h
    · rw [mul_div_assoc]
    · rfl
  refine ⟨?_, ?_⟩
  · intro i hi
    rw [heq]; exact hpne.1 i hi
  · intro i hi
    rw [heq]; exact hpne.2 i hi
