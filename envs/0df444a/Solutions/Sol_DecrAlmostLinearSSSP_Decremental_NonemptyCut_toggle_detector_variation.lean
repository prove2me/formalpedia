-- Prove2me | solution 1 for DecrAlmostLinearSSSP.Decremental.NonemptyCut.toggle_detector_variation
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-22T23:01:41.148034+00:00
-- url     : https://prove2.me/submissions/3fe9850f-806a-4381-8f83-ffeedccb3a3e

import Definitions.Def_DecrAlmostLinearSSSP_NonemptyCutProtocol

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal
open DecrAlmostLinearSSSP.Decremental DecrAlmostLinearSSSP.Decremental.NonemptyCut

/-- One toggle increases the total capacity-weighted detector displacement by at most one. -/
theorem solution {n k : ℕ} (g : Physical n k)
    (y : Fin n → ℝ) (b : Fin k → ℝ) (C : Finset (Fin n)) (tau U : ℝ)
    (hu : ∀ e ∈ g.active, 0 ≤ g.u e)
    (hcap : cutCapacity g C ≤ U) (htau0 : 0 ≤ tau) (htauU : tau ≤ 1 / U) :
    (∑ e ∈ g.active, g.u e *
      |(y (g.graph.tail e) + if g.graph.tail e ∈ C then tau else 0) -
        (y (g.graph.head e) + if g.graph.head e ∈ C then tau else 0) - b e|) ≤
    (∑ e ∈ g.active, g.u e * |y (g.graph.tail e) - y (g.graph.head e) - b e|) + 1 := by
  classical
  let z : Fin n → ℝ := fun v => y v + if v ∈ C then tau else 0
  have hper : ∀ e ∈ g.active,
      g.u e * |z (g.graph.tail e) - z (g.graph.head e) - b e| ≤
        g.u e * |y (g.graph.tail e) - y (g.graph.head e) - b e| +
          tau * (if (g.graph.tail e ∈ C) ≠ (g.graph.head e ∈ C) then g.u e else 0) := by
    intro e he
    have hdelta : |(z (g.graph.tail e) - z (g.graph.head e) - b e) -
        (y (g.graph.tail e) - y (g.graph.head e) - b e)| ≤
          tau * (if (g.graph.tail e ∈ C) ≠ (g.graph.head e ∈ C) then 1 else 0) := by
      by_cases ht : g.graph.tail e ∈ C <;> by_cases hh : g.graph.head e ∈ C <;>
        simp [z, ht, hh, htau0, abs_of_nonneg]
    have htri : |z (g.graph.tail e) - z (g.graph.head e) - b e| ≤
        |y (g.graph.tail e) - y (g.graph.head e) - b e| +
          tau * (if (g.graph.tail e ∈ C) ≠ (g.graph.head e ∈ C) then 1 else 0) := by
      have h0 := abs_add_le (y (g.graph.tail e) - y (g.graph.head e) - b e)
        ((z (g.graph.tail e) - z (g.graph.head e) - b e) -
          (y (g.graph.tail e) - y (g.graph.head e) - b e))
      have heq : (y (g.graph.tail e) - y (g.graph.head e) - b e) +
          ((z (g.graph.tail e) - z (g.graph.head e) - b e) -
            (y (g.graph.tail e) - y (g.graph.head e) - b e)) =
          z (g.graph.tail e) - z (g.graph.head e) - b e := by ring
      rw [heq] at h0
      exact h0.trans (add_le_add_right hdelta _)
    calc
      g.u e * |z (g.graph.tail e) - z (g.graph.head e) - b e| ≤
          g.u e * (|y (g.graph.tail e) - y (g.graph.head e) - b e| +
            tau * (if (g.graph.tail e ∈ C) ≠ (g.graph.head e ∈ C) then 1 else 0)) :=
        mul_le_mul_of_nonneg_left htri (hu e he)
      _ = _ := by
        by_cases hc : (g.graph.tail e ∈ C) ≠ (g.graph.head e ∈ C) <;> simp [hc] <;> ring
  calc
    (∑ e ∈ g.active, g.u e *
      |(y (g.graph.tail e) + if g.graph.tail e ∈ C then tau else 0) -
        (y (g.graph.head e) + if g.graph.head e ∈ C then tau else 0) - b e|) =
        ∑ e ∈ g.active, g.u e * |z (g.graph.tail e) - z (g.graph.head e) - b e| := rfl
    _ ≤ ∑ e ∈ g.active, (g.u e * |y (g.graph.tail e) - y (g.graph.head e) - b e| +
          tau * (if (g.graph.tail e ∈ C) ≠ (g.graph.head e ∈ C) then g.u e else 0)) :=
      Finset.sum_le_sum hper
    _ = (∑ e ∈ g.active, g.u e * |y (g.graph.tail e) - y (g.graph.head e) - b e|) +
          tau * cutCapacity g C := by
      rw [Finset.sum_add_distrib]
      congr 1
      unfold cutCapacity
      rw [Finset.mul_sum]
    _ ≤ (∑ e ∈ g.active, g.u e * |y (g.graph.tail e) - y (g.graph.head e) - b e|) + 1 := by
      have hprod : tau * cutCapacity g C ≤ 1 := by
        calc
          tau * cutCapacity g C ≤ tau * U := mul_le_mul_of_nonneg_left hcap htau0
          _ ≤ (1 / U) * U := by
            by_cases hU : 0 ≤ U
            · exact mul_le_mul_of_nonneg_right htauU hU
            · have hUn : U < 0 := lt_of_not_ge hU
              have hrecip : 1 / U < 0 := div_neg_of_pos_of_neg zero_lt_one hUn
              linarith
          _ ≤ 1 := by
            by_cases hU : U = 0
            · simp [hU]
            · rw [one_div, inv_mul_cancel₀ hU]
      linarith
