-- Prove2me | solution 1 for ConsistentSubmodular.GridStream.rows_after_stage
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:32:49.618461+00:00
-- url     : https://prove2.me/submissions/947745cd-3a89-4fb9-aa1f-a5c912472dcd

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Impossibility_GridStreamCoverage
import Theorems.Thm_ConsistentSubmodular_GridStream_coverage_le
import Theorems.Thm_ConsistentSubmodular_GridStream_card_stageColumns
import Theorems.Thm_ConsistentSubmodular_GridStream_coverage_stage

section

noncomputable section

open scoped BigOperators

open Finset

namespace ConsistentSubmodular.GridStream

theorem rowsHeld_le_card (k : ℕ) {N : ℕ} (S : Finset (Fin N)) : rowsHeld k S ≤ S.card :=
  card_filter_le _ _

/-- Division with remainder for `a n + b` with `b < n`. -/
theorem mul_add_div_mod {a b n : ℕ} (hb : b < n) : (a * n + b) / n = a ∧ (a * n + b) % n = b := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le b) hb
  refine ⟨?_, ?_⟩
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hb, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]

/-- A column set present at time `t` is from a stage at most `(t - 1) / k`: the
set `b_{i,j}` sits at the position `j k + i - 1 < t`, and its stage index in the
cover is `(e - k) / k = j - 1`. -/
theorem stage_lt_of_arrived {k N t : ℕ} (hk : 0 < k) {S : Finset (Fin N)}
    (hS : S ⊆ arrivedPrefix N t) : ∀ e ∈ S, k ≤ e.val → (e.val - k) / k < (t - 1) / k := by
  intro e he hke
  have het : e.val < t := by
    have := hS he
    simp only [arrivedPrefix, mem_filter, mem_univ, true_and] at this
    exact this
  have h1 : (e.val - k) / k + 1 = e.val / k := by
    rw [← Nat.add_div_right _ hk, Nat.sub_add_cancel hke]
  have h2 : e.val / k ≤ (t - 1) / k := Nat.div_le_div_right (by omega)
  omega

theorem stageColumns_subset {k m j t : ℕ} (ht : (j + 1) * k ≤ t) :
    stageColumns k m j ⊆ arrivedPrefix (k + m * k) t := by
  intro e he
  simp only [stageColumns, arrivedPrefix, mem_filter, mem_univ, true_and] at he ⊢
  omega

end ConsistentSubmodular.GridStream

end

end

section

open scoped BigOperators
open Finset
open ConsistentSubmodular ConsistentSubmodular.GridStream
variable {k m C : ℕ} {S : Fin (k + m * k + 1) → Finset (Fin (k + m * k))}

theorem solution (hk : 0 < k) (hm : k ≤ m) (hS : FeasibleTrajectory k C S)
    (happrox : ∀ (t : Fin (k + m * k + 1)) (A : Finset (Fin (k + m * k))),
      A ⊆ arrivedPrefix (k + m * k) t.val → A.card ≤ k →
      3 / 4 * coverageValue (gridStreamCover k m) A ≤
        coverageValue (gridStreamCover k m) (S t)) :
    3 * rowsHeld k (S ⟨k + k * k, by
      have := Nat.mul_le_mul_right k hm
      omega⟩) ≤ k := by
  have hmk := Nat.mul_le_mul_right k hm
  set t₁ : Fin (k + m * k + 1) := ⟨k + k * k, by omega⟩
  -- The competitor `B_k`, the columns of stage `k`.
  have hsub : stageColumns k m k ⊆ arrivedPrefix (k + m * k) t₁.val :=
    stageColumns_subset (le_of_eq (by simp only [t₁]; ring))
  have hA := happrox t₁ _ hsub (card_stageColumns hm).le
  have hstage := coverage_stage (k := k) (m := m) (j := k) hk hm
  -- At time `k (k + 1)` the trajectory holds column sets from the stages up to `k`.
  have hJ : (t₁.val - 1) / k = k := by
    simp only [t₁]
    rw [show k + k * k - 1 = k * k + (k - 1) by omega]
    exact (mul_add_div_mod (by omega)).1
  have hst := stage_lt_of_arrived hk (hS.2.1 t₁).1
  rw [hJ] at hst
  have hcov := coverage_le (S t₁) k (hS.2.1 t₁).2 hst
  have hn := (rowsHeld_le_card k (S t₁)).trans (hS.2.1 t₁).2
  set n := rowsHeld k (S t₁)
  have hnR : (n : ℝ) ≤ k := by exact_mod_cast hn
  -- `3/4 · 2k² ≤ n k + (k - n) 2k - n (k - n)`, that is `4 n² - 8 k n + 2 k² ≥ 0`.
  have hquad : 0 ≤ 4 * (n : ℝ) ^ 2 - 8 * k * n + 2 * k ^ 2 := by
    nlinarith
  -- With `n ≤ k` this forces `n ≤ (1 - √2/2) k ≤ k/3`.
  by_contra hcon
  have h3 : k + 1 ≤ 3 * n := by omega
  have h3R : (k : ℝ) + 1 ≤ 3 * n := by exact_mod_cast h3
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith [mul_nonneg (sub_nonneg.mpr h3R) (by linarith : (0 : ℝ) ≤ 5 * k - 1 - 3 * n)]

end
