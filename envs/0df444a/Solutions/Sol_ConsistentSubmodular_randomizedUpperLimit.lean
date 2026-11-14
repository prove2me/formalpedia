-- Prove2me | solution 1 for ConsistentSubmodular.randomizedUpperLimit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:44:28.645374+00:00
-- url     : https://prove2.me/submissions/201104ee-1b45-4b76-a7aa-2fa7838500d5

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements
import Theorems.Thm_ConsistentSubmodular_randomizedUpper

section

noncomputable section

open scoped BigOperators

open Finset

namespace ConsistentSubmodular.HardInstance

/-- **Remark 1** from Theorem 1: for a fixed consistency bound `C` and `δ > 0`,
take `ε` with `K ε < δ`; every sufficiently large `k` has `C ≤ ⌊ε k⌋`. -/
theorem randomizedUpperLimit_of (h : RandomizedUpperGoal) : RandomizedUpperLimitGoal := by
  intro C δ hδ
  obtain ⟨K, hK⟩ := h
  set ε : ℝ := min 1 (δ / (2 * (|K| + 1))) with hε
  have hε0 : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hKε : K * ε < δ := by
    have hle : ε ≤ δ / (2 * (|K| + 1)) := min_le_right _ _
    have h1 : K * ε ≤ |K| * ε := mul_le_mul_of_nonneg_right (le_abs_self K) hε0.le
    have h2 : |K| * ε ≤ |K| * (δ / (2 * (|K| + 1))) :=
      mul_le_mul_of_nonneg_left hle (abs_nonneg K)
    have h3 : |K| * (δ / (2 * (|K| + 1))) < δ := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [abs_nonneg K]
    linarith
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt ((C + 1) / ε)
  refine ⟨k₀, fun k hk₀k => ?_⟩
  have hk : (C + 1) / ε < k := hk₀.trans_le (by exact_mod_cast hk₀k)
  have hkpos : 0 < k := by
    have : (0 : ℝ) < k := lt_trans (by positivity) hk
    exact_mod_cast this
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hεk : C + 1 < ε * k := by
    rw [div_lt_iff₀ hε0] at hk
    linarith
  have hinv : 1 / (k : ℝ) ≤ ε := by
    rw [div_le_iff₀ hkR]
    nlinarith
  obtain ⟨n, u, cover, hcover⟩ := hK k ε hkpos hinv hε1
  refine ⟨n, u, cover, fun μ hμ => ?_⟩
  have hCfloor : C ≤ ⌊ε * k⌋₊ := Nat.le_floor (by linarith)
  have hμ' : μ.Feasible k ⌊ε * k⌋₊ := fun S hS =>
    let hF := hμ S hS
    ⟨hF.1, hF.2.1, fun t => (hF.2.2 t).trans hCfloor⟩
  obtain ⟨t, A, hA, hcard, hpos, hle⟩ := hcover μ hμ'
  refine ⟨t, A, hA, hcard, lt_of_le_of_lt hle ?_⟩
  exact mul_lt_mul_of_pos_right (by linarith) hpos

end ConsistentSubmodular.HardInstance

end

end

section

open ConsistentSubmodular

theorem solution : RandomizedUpperLimitGoal :=
  HardInstance.randomizedUpperLimit_of randomizedUpper

end
