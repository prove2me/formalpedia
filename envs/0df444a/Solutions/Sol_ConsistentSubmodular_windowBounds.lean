-- Prove2me | solution 1 for ConsistentSubmodular.windowBounds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:34:36.139572+00:00
-- url     : https://prove2.me/submissions/68a4c747-cb74-4580-aef7-cb41aff2125e

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_Model

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {ι : Type*} [DecidableEq ι]

namespace WindowInstance

variable {n : ℕ} (W : WindowInstance n)

theorem arrivalValue_mono : Monotone W.arrivalValue := fun _ _ hsj =>
  W.objective.monotone _ _ (W.arrivals_mono hsj)

theorem benchmark_mono : Monotone W.benchmark := by
  intro s j hsj
  unfold benchmark
  exact (W.objective.monotone _ _ (Finset.union_subset_union_right (W.arrivals_mono hsj))).trans
    (W.candidate_optimal j _ (W.candidate_subset s) (W.candidate_card s))

/-- The optimum grows no faster than the arrivals alone, the second chain of
(19): `P_j - P_s ≤ λ_j - λ_s` for `s ≤ j`. The candidate `O_j` is feasible at
stage `s`, and diminishing returns compare the arrivals with and without it. -/
theorem benchmark_growth {s j : Fin (W.lastStage + 1)} (hsj : s ≤ j) :
    W.benchmark j - W.benchmark s ≤ W.arrivalValue j - W.arrivalValue s := by
  have hopt := W.candidate_optimal s (W.candidate j) (W.candidate_subset j) (W.candidate_card j)
  have hdr := W.objective.diminishing_returns
    (Finset.subset_union_right : W.arrivals s ⊆ W.candidate j ∪ W.arrivals s) (W.arrivals j)
  have h1 : (W.candidate j ∪ W.arrivals s) ∪ W.arrivals j = W.candidate j ∪ W.arrivals j := by
    rw [Finset.union_assoc, Finset.union_eq_right.mpr (W.arrivals_mono hsj)]
  rw [h1, Finset.union_eq_right.mpr (W.arrivals_mono hsj)] at hdr
  unfold benchmark arrivalValue
  linarith

theorem gain_antitone {s j : Fin (W.lastStage + 1)} (hsj : s ≤ j) : W.gain j ≤ W.gain s := by
  have h := W.benchmark_growth hsj
  unfold gain
  linarith

/-- `g_j ≥ 0`, because the empty core is feasible. -/
theorem gain_nonneg (j : Fin (W.lastStage + 1)) : 0 ≤ W.gain j := by
  have h := W.candidate_optimal j ∅ (Finset.empty_subset _) (by simp)
  rw [Finset.empty_union] at h
  unfold gain benchmark arrivalValue
  linarith

/-- `g_j ≤ V`: the residual decreases from `g_0 = V - f(∅)`. -/
theorem gain_le_benchmark_zero (j : Fin (W.lastStage + 1)) : W.gain j ≤ W.benchmark 0 := by
  have h := W.gain_antitone (Fin.zero_le j)
  have h0 := W.objective.nonnegative ∅
  have hg0 : W.gain 0 = W.benchmark 0 - W.objective.value ∅ := by
    simp [gain, arrivalValue, W.arrivals_zero]
  linarith

end WindowInstance

namespace WindowBounds

/-- **Lemma B.1** (window bounds). -/
theorem windowBounds : WindowBoundsGoal := fun _ W =>
  ⟨W.arrivalValue_mono, W.benchmark_mono, fun _ _ hsj => W.gain_antitone hsj,
    fun _ j hsj => ⟨W.gain_nonneg j, W.gain_le_benchmark_zero j, W.benchmark_mono (Fin.zero_le j),
      sub_nonneg.mpr (W.benchmark_mono hsj), W.benchmark_growth hsj⟩⟩

end WindowBounds

end ConsistentSubmodular

end

end

section

open ConsistentSubmodular

theorem solution : WindowBoundsGoal :=
  WindowBounds.windowBounds

end
