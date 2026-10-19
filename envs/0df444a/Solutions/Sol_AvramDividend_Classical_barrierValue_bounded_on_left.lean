-- Prove2me | solution 1 for AvramDividend.Classical.barrierValue_bounded_on_left
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T06:03:06.983047+00:00
-- url     : https://prove2.me/submissions/806663d3-bc67-49c4-928f-ed48a2dfd93f

import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Data.EReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    (W : ℝ → ℝ) (a x : ℝ) (ha : 0 ≤ a) (hx : a < x)
    (hn : ∀ z, 0 ≤ z → 0 ≤ W z)
    (hm : MonotoneOn W (Ici 0)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℝ, z ≤ x → |barrierValue W a z| ≤ M := by
  let d : EReal := scaleDeriv W a
  let B : ℝ := W a * |(d.toReal)⁻¹|
  let M : ℝ := max B ((x - a) + |divE (W a) d|)
  have hB : 0 ≤ B := mul_nonneg (hn a ha) (abs_nonneg _)
  have hM : 0 ≤ M := hB.trans (le_max_left _ _)
  have hsmall : ∀ z, 0 ≤ z → z ≤ a → |divE (W z) d| ≤ B := by
    intro z hz hza
    have hw : W z ≤ W a :=
      hm (mem_Ici.mpr hz) (mem_Ici.mpr ha) hza
    by_cases ht : d = ⊤
    · simp [divE, ht, B]
    · have hdiv : divE (W z) d = W z * (d.toReal)⁻¹ := by
        simp [divE, ht, div_eq_mul_inv]
      rw [hdiv, abs_mul, abs_of_nonneg (hn z hz)]
      exact mul_le_mul_of_nonneg_right hw (abs_nonneg _)
  refine ⟨M, hM, ?_⟩
  intro z hz
  by_cases hneg : z < 0
  · have hv : barrierValue W a z = 0 := by simp [barrierValue, hneg]
    simpa [hv] using hM
  by_cases hza : z ≤ a
  · have hv : barrierValue W a z = divE (W z) d := by
      simp [barrierValue, hneg, hza, d]
    rw [hv]
    exact (hsmall z (le_of_not_gt hneg) hza).trans (le_max_left _ _)
  · have haz : a < z := lt_of_not_ge hza
    have hv : barrierValue W a z = z - a + divE (W a) d := by
      simp [barrierValue, hneg, hza, d]
    rw [hv]
    have hza0 : 0 ≤ z - a := sub_nonneg.mpr haz.le
    calc
      |z - a + divE (W a) d| ≤ |z - a| + |divE (W a) d| := abs_add_le _ _
      _ = (z - a) + |divE (W a) d| := by rw [abs_of_nonneg hza0]
      _ ≤ (x - a) + |divE (W a) d| := by linarith
      _ ≤ M := le_max_right _ _
