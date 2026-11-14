-- Prove2me | solution 1 for ConsistentSubmodular.deterministicUpperLimit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:39:02.86921+00:00
-- url     : https://prove2.me/submissions/364c6714-b89c-4374-a3d7-828063d92e3c

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements
import Theorems.Thm_ConsistentSubmodular_deterministicUpper

section

noncomputable section

open scoped BigOperators

open Finset

namespace ConsistentSubmodular.GridStream

/-- The impossibility of Main Result 2 for constant recourse, from Theorem 3:
choose `ε` with `3/4 + K ε < α` and a budget `k` with `C ≤ ⌊ε k⌋`. -/
theorem deterministicUpperLimit_of (h : DeterministicUpperGoal) : DeterministicUpperLimitGoal := by
  obtain ⟨K, hK⟩ := h
  intro α hα C
  set ε : ℝ := min 1 ((α - 3 / 4) / (2 * (|K| + 1))) with hεdef
  have hgap : 0 < α - 3 / 4 := by linarith
  have hK1 : 0 < |K| + 1 := by positivity
  have hε0 : 0 < ε := lt_min one_pos (div_pos hgap (by positivity))
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hKε : 3 / 4 + K * ε < α := by
    have hle : ε ≤ (α - 3 / 4) / (2 * (|K| + 1)) := min_le_right _ _
    have h1 : K * ε ≤ |K| * ε := mul_le_mul_of_nonneg_right (le_abs_self K) hε0.le
    have h2 : (|K| + 1) * ε ≤ (α - 3 / 4) / 2 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      rw [le_div_iff₀ (by positivity)] at hle
      nlinarith
    nlinarith
  obtain ⟨k, hk⟩ := exists_nat_ge (((C : ℝ) + 1) / ε)
  have hCk : (C : ℝ) + 1 ≤ ε * k := by
    rw [div_le_iff₀ hε0] at hk
    linarith
  have hkpos : 0 < k := by
    have : (0 : ℝ) < k := by nlinarith [Nat.cast_nonneg (α := ℝ) C]
    exact_mod_cast this
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hεk : 1 / (k : ℝ) ≤ ε := by
    rw [div_le_iff₀ hkR]
    nlinarith [Nat.cast_nonneg (α := ℝ) C]
  have hCfloor : C ≤ ⌊ε * k⌋₊ := Nat.le_floor (by linarith)
  obtain ⟨n, u, cover, hcover⟩ := hK k ε hkpos hεk hε1
  refine ⟨n, k, u, cover, fun S hS => ?_⟩
  have hS' : FeasibleTrajectory k ⌊ε * k⌋₊ S :=
    ⟨hS.1, hS.2.1, fun t => (hS.2.2 t).trans hCfloor⟩
  obtain ⟨t, A, hA, hAc, hpos, hle⟩ := hcover S hS'
  exact ⟨t, A, hA, hAc, by nlinarith⟩

end ConsistentSubmodular.GridStream

end

end

section

open ConsistentSubmodular

theorem solution : DeterministicUpperLimitGoal :=
  GridStream.deterministicUpperLimit_of deterministicUpper

end
