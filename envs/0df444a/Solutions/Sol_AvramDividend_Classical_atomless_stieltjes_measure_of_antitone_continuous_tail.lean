-- Prove2me | solution 1 for AvramDividend.Classical.atomless_stieltjes_measure_of_antitone_continuous_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T07:25:37.607573+00:00
-- url     : https://prove2.me/submissions/08437e08-df13-483c-94f4-e0f5e7a687a5

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter
open scoped Topology ENNReal

theorem solution
    (g : ℝ → ℝ) (hcont : Continuous g)
    (hanti : Antitone g) (hnonneg : ∀ x : ℝ, 0 ≤ g x)
    (hlim : Tendsto g atTop (𝓝 (0 : ℝ))) :
    ∃ μ : Measure ℝ,
      NullSingletonClass μ ∧
      (∀ x : ℝ, μ (Ici x) ≠ ⊤) ∧
      (∀ x : ℝ, μ.real (Ici x) = g x) := by
  let F : StieltjesFunction ℝ :=
    { toFun := fun x => -g x
      mono' := by
        intro x y hxy
        exact neg_le_neg (hanti hxy)
      right_continuous' := by
        intro x
        exact (hcont.neg.continuousAt).continuousWithinAt }
  have hFcont : Continuous (F : ℝ → ℝ) := hcont.neg
  have hFtop : Tendsto (F : ℝ → ℝ) atTop (𝓝 (0 : ℝ)) := by
    change Tendsto (fun x : ℝ => -g x) atTop (𝓝 (0 : ℝ))
    simpa using hlim.neg
  have hFleft (x : ℝ) : Function.leftLim F x = F x := by
    apply ContinuousWithinAt.leftLim_eq
    exact (hFcont.continuousAt).continuousWithinAt
  let μ : Measure ℝ := F.measure
  have hsingleton (x : ℝ) : μ {x} = 0 := by
    change F.measure {x} = 0
    rw [F.measure_singleton x, hFleft x]
    simp
  have hnull : NullSingletonClass μ :=
    ⟨hsingleton⟩
  have htail (x : ℝ) : μ (Ici x) = ENNReal.ofReal (g x) := by
    change F.measure (Ici x) = ENNReal.ofReal (g x)
    rw [F.measure_Ici hFtop x, hFleft x]
    change ENNReal.ofReal (0 - -g x) = ENNReal.ofReal (g x)
    simp
  refine ⟨μ, hnull, ?_, ?_⟩
  · intro x
    rw [htail x]
    exact ENNReal.ofReal_ne_top
  · intro x
    change (μ (Ici x)).toReal = g x
    rw [htail x, ENNReal.toReal_ofReal (hnonneg x)]
