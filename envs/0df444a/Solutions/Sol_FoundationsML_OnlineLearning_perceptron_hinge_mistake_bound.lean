-- Prove2me | solution 1 for FoundationsML.OnlineLearning.perceptron_hinge_mistake_bound
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:14:13.197372+00:00
-- url     : https://prove2.me/submissions/35b268f1-1ecf-49ea-8cb1-839796f570ab

import Mathlib
import Definitions.Def_FoundationsML_OnlineLearning_PerceptronNumUpdates
import Definitions.Def_FoundationsML_OnlineLearning_PerceptronUpdates

namespace FoundationsML.OnlineLearning

/-- With the zero input sequence, the Perceptron updates at round `0` (the weight is `0`). -/
theorem aux_phmb_updates :
    PerceptronUpdates (V := ℝ) (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) 1 = {0} := by
  unfold PerceptronUpdates
  ext t
  simp

end FoundationsML.OnlineLearning

open FoundationsML.OnlineLearning

theorem solution : ¬ (∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (x : ℕ → V) (y : ℕ → ℝ) (hy : ∀ t, y t = 1 ∨ y t = -1)
    (T : ℕ) (r : ℝ) (hr : 0 < r) (hxr : ∀ t < T, ‖x t‖ ≤ r),
    (PerceptronNumUpdates x y T : ℝ) ≤
      ⨅ ρ ∈ Set.Ioi (0 : ℝ), ⨅ v ∈ Metric.closedBall (0 : V) 1,
        ((r / ρ + Real.sqrt (r ^ 2 / ρ ^ 2 +
            4 * ∑ t ∈ PerceptronUpdates x y T,
              max 0 (1 - y t * (inner (𝕜 := ℝ) v (x t) : ℝ) / ρ))) /
          2) ^ 2) := by
  intro h
  have H := h (V := ℝ) (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (fun _ => Or.inl rfl) 1 1
    one_pos (by intro t _; simp)
  set F : ℝ → ℝ := fun ρ => ⨅ (_ : ρ ∈ Set.Ioi (0 : ℝ)), ⨅ v ∈ Metric.closedBall (0 : ℝ) 1,
        ((1 / ρ + Real.sqrt (1 ^ 2 / ρ ^ 2 +
            4 * ∑ t ∈ PerceptronUpdates (V := ℝ) (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) 1,
              max 0 (1 - (fun _ => (1 : ℝ)) t * (inner (𝕜 := ℝ) v ((fun _ => (0 : ℝ)) t) : ℝ) / ρ))) /
          2) ^ 2 with hF
  have hnn : ∀ ρ, 0 ≤ F ρ := by
    intro ρ
    refine Real.iInf_nonneg fun _ => Real.iInf_nonneg fun v => Real.iInf_nonneg fun _ => ?_
    positivity
  have hbdd : BddBelow (Set.range F) := ⟨0, by rintro _ ⟨ρ, rfl⟩; exact hnn ρ⟩
  have hneg : F (-1) = 0 := by
    have : IsEmpty ((-1 : ℝ) ∈ Set.Ioi (0 : ℝ)) := ⟨fun h => by norm_num at h⟩
    simp only [hF]
    exact Real.iInf_of_isEmpty _
  have hle : (⨅ ρ, F ρ) ≤ 0 := hneg ▸ ciInf_le hbdd (-1)
  have hcard : (PerceptronNumUpdates (V := ℝ) (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) 1 : ℝ) = 1 := by
    unfold PerceptronNumUpdates
    rw [aux_phmb_updates]
    simp
  have : (1 : ℝ) ≤ 0 := by
    calc (1 : ℝ) = _ := hcard.symm
      _ ≤ _ := H
      _ ≤ 0 := hle
  linarith
