-- Prove2me | solution 1 for BianchiIX.exists_retained_era_parameter_budget
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T07:04:16.386837+00:00
-- url     : https://prove2.me/submissions/c6e83a32-856c-47aa-971f-0d8f74c216f8

import Theorems.Thm_BianchiIX_exists_common_rpow_budget
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set


/-- One amplitude threshold supplies all local smallness conditions for every retained digit. -/
theorem solution {ε C σ : ℝ} {J : ℕ}
    (hε : 0 < ε) (hC : 0 ≤ C) (hσ : 0 < σ) (hσone : σ < 1)
    (hσJ : σ * (2 * J : ℕ) < 1) :
    ∃ Bstar : ℝ, 0 < Bstar ∧ Bstar < 1 ∧ ∀ B ∈ Ioc 0 Bstar,
      let β := B ^ σ
      0 < β ∧ β < 1 / 160 ∧ B ≤ ε * (β / 2) ^ (2 * J) ∧ C * B < β / 4 ∧
      ∀ m : ℕ, (m : ℝ) + 1 ≤ 1 / β → B * (2 * ((m : ℝ) + 2 - β)) ≤ ε := by
  obtain ⟨Bstar, hBs, hBsone, HB⟩ := exists_common_rpow_budget (ι := Fin 4) Finset.univ
    (C := ![4, (2 : ℝ) ^ (2 * J), 4 * C, 1])
    (p := ![1 - σ, 1 - σ * (2 * J : ℕ), 1 - σ, σ])
    (ε := ![ε, ε, 1, 1 / 160])
    (by intro i _; fin_cases i <;> dsimp <;> positivity)
    (by intro i _; fin_cases i <;> dsimp <;> linarith)
    (by intro i _; fin_cases i <;> dsimp <;> positivity) (by norm_num : (0 : ℝ) < 1)
  refine ⟨Bstar, hBs, hBsone, ?_⟩
  intro B hB β
  have hβ : 0 < β := Real.rpow_pos_of_pos hB.1 _
  have hscale : 4 * B ^ (1 - σ) < ε := HB B hB 0 (Finset.mem_univ _)
  have hterminal : (2 : ℝ) ^ (2 * J) * B ^ (1 - σ * (2 * J : ℕ)) < ε :=
    HB B hB 1 (Finset.mem_univ _)
  have hmargin : 4 * C * B ^ (1 - σ) < 1 := HB B hB 2 (Finset.mem_univ _)
  have hβmax : β < 1 / 160 := by simpa using HB B hB 3 (Finset.mem_univ _)
  have hfactor : B = B ^ (1 - σ) * β := by
    dsimp [β]
    rw [← Real.rpow_add hB.1, sub_add_cancel, Real.rpow_one]
  have hfactorJ : B = B ^ (1 - σ * (2 * J : ℕ)) * β ^ (2 * J) := by
    dsimp [β]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hB.1.le, ← Real.rpow_add hB.1,
      sub_add_cancel, Real.rpow_one]
  refine ⟨hβ, hβmax, ?_, ?_, ?_⟩
  · rw [div_pow, ← mul_div_assoc]
    apply (le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) _)).mpr
    calc
      B * 2 ^ (2 * J) = ((2 : ℝ) ^ (2 * J) * B ^ (1 - σ * (2 * J : ℕ))) * β ^ (2 * J) := by
        exact (congrArg (fun x : ℝ => x * 2 ^ (2 * J)) hfactorJ).trans (by ring)
      _ ≤ ε * β ^ (2 * J) := mul_le_mul_of_nonneg_right hterminal.le (pow_nonneg hβ.le _)
  · calc
      C * B = (4 * C * B ^ (1 - σ)) * β / 4 :=
        (congrArg (fun x : ℝ => C * x) hfactor).trans (by ring)
      _ < 1 * β / 4 := div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hmargin hβ) (by norm_num)
      _ = β / 4 := by ring
  · intro m hm
    have hmβ := (le_div_iff₀ hβ).mp hm
    have hbound : β * (2 * ((m : ℝ) + 2 - β)) ≤ 4 := by nlinarith [sq_nonneg β]
    calc
      B * (2 * ((m : ℝ) + 2 - β)) = B ^ (1 - σ) * (β * (2 * ((m : ℝ) + 2 - β))) := by
        exact (congrArg (fun x : ℝ => x * (2 * ((m : ℝ) + 2 - β))) hfactor).trans (by ring)
      _ ≤ B ^ (1 - σ) * 4 := mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hB.1.le _)
      _ ≤ ε := by nlinarith only [hscale]
