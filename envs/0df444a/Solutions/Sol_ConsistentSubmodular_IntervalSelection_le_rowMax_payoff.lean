-- Prove2me | solution 1 for ConsistentSubmodular.IntervalSelection.le_rowMax_payoff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:34:12.005116+00:00
-- url     : https://prove2.me/submissions/8082269d-b92a-4d60-8fed-53f4f6ed1bc4

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_IntervalSelection
import Theorems.Thm_ConsistentSubmodular_IntervalSelection_value_le_objective

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.IntervalSelection

section Intervals

variable {N : ℕ} (I : IntervalInstance N)

/-- An interval is worth its right endpoint at its own realization. -/
theorem value_self (j : Fin (N + 1)) : I.value j j = I.right j := by
  unfold IntervalInstance.value
  rw [max_self, max_eq_right (sub_nonneg.mpr (I.left_le_right j))]
  ring

end Intervals

end ConsistentSubmodular.IntervalSelection

end

end

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.IntervalSelection
variable {n : ℕ} (W : WindowInstance n)

theorem solution {α : ℝ} (hα0 : 0 ≤ α)
    (hgap : ∀ (N : ℕ) (I : IntervalInstance N), α ≤ I.adaptivityGap)
    (hpos : ∀ j, 0 < W.benchmark j) (β : Point W.lastStage) (hβ : IsSimplex β) :
    α ≤ Minimax.rowMax W.payoff β := by
  classical
  let F : Fin (W.lastStage + 1) → Fin (W.lastStage + 1) → ℝ :=
    fun i j => W.objective.value (W.candidate i ∪ W.arrivals j)
  -- Reweight the adversary's distribution `β` by the benchmarks `r_j`.
  have hterm (j : Fin (W.lastStage + 1)) : 0 ≤ β j / W.benchmark j :=
    div_nonneg (hβ.1 j) (hpos j).le
  set Z := ∑ j, β j / W.benchmark j with hZ
  have hZpos : 0 < Z := by
    rcases (Finset.sum_nonneg fun j _ => hterm j).lt_or_eq with h | h
    · exact h
    · exfalso
      have hzero := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hterm j).mp h.symm
      have hβ0 : ∑ j, β j = 0 := Finset.sum_eq_zero fun j hj => by
        have hj' := hzero j hj
        rwa [div_eq_zero_iff, or_iff_left (hpos j).ne'] at hj'
      rw [hβ.2] at hβ0
      norm_num at hβ0
  let p : Point W.lastStage := fun j => β j / W.benchmark j / Z
  have hp : IsSimplex p := ⟨fun j => div_nonneg (hterm j) hZpos.le, by
    simp only [p]
    rw [← Finset.sum_div, ← hZ, div_self hZpos.ne']⟩
  let I := windowIntervals W p hp
  -- The value in hindsight is at least `E_p[v(j, j)] = E_p[r_j] = 1 / Z`.
  have hadapt : 1 / Z ≤ I.adaptiveValue := by
    have hEr : ∑ j, p j * W.benchmark j = 1 / Z := by
      have hj (j : Fin (W.lastStage + 1)) : p j * W.benchmark j = β j / Z := by
        simp only [p]
        field_simp [(hpos j).ne', hZpos.ne']
      simp only [hj]
      rw [← Finset.sum_div, hβ.2]
    rw [← hEr]
    refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (hp.1 j)
    have hself := value_self I j
    have hle := Finset.le_sup' (fun i => I.value i j) (Finset.mem_univ j)
    rw [hself] at hle
    exact hle
  have hadaptPos : 0 < I.adaptiveValue := lt_of_lt_of_le (by positivity) hadapt
  -- The gap hypothesis: `α · E_p[max_h v(h, j)] ≤ max_i E_p[v(i, j)]`.
  have hfix : α * I.adaptiveValue ≤ I.fixedValue := by
    have hgapI := hgap _ I
    unfold IntervalInstance.adaptivityGap at hgapI
    rw [if_neg hadaptPos.ne', le_div_iff₀ hadaptPos] at hgapI
    exact hgapI
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    fun i => ∑ j, I.prob j * I.value i j
  -- The row of the best fixed interval is worth at least `α` against `β`.
  have hrow : α ≤ ∑ j, β j * W.payoff i j := by
    have hscale : ∑ j, β j * W.payoff i j = Z * ∑ j, p j * F i j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [WindowInstance.payoff, p, F]
      field_simp [(hpos j).ne', hZpos.ne']
    rw [hscale]
    calc α = Z * (α * (1 / Z)) := by field_simp
      _ ≤ Z * (α * I.adaptiveValue) := by gcongr
      _ ≤ Z * I.fixedValue := by gcongr
      _ = Z * ∑ j, p j * I.value i j := by rw [IntervalInstance.fixedValue, hi]; rfl
      _ ≤ Z * ∑ j, p j * F i j := by
        gcongr with j
        · exact hp.1 j
        · exact value_le_objective W p hp i j
  exact hrow.trans (Finset.le_sup' (fun i => ∑ j, β j * W.payoff i j) (Finset.mem_univ i))

end
