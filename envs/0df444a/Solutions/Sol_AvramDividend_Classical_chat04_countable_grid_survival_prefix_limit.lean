-- Prove2me | solution 1 for AvramDividend.Classical.chat04_countable_grid_survival_prefix_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T07:44:17.394195+00:00
-- url     : https://prove2.me/submissions/d2b0f2d0-3a05-41ab-880c-a24e261ff0f8

import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
import Theorems.Thm_AvramDividend_Classical_chat04_antitone_grid_survival_lintegral_iInf

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-!
Continuity of expected terminal payoff from finite-prefix survival checks to
all countably many checks. The prefix events form a measurable antitone
family, and their intersection is exactly the full event intersection.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (B : ℕ → Set Ω) (hB : ∀ k, MeasurableSet (B k))
    (g : Ω → ℝ≥0∞) (hg : Measurable g)
    (hFin : (∫⁻ ω, g ω ∂P) ≠ ∞) :
    (∫⁻ ω, (⋂ k, B k).indicator g ω ∂P) =
      ⨅ n, ∫⁻ ω,
        ({ω | ∀ k ≤ n, ω ∈ B k}).indicator g ω ∂P := by
  let A : ℕ → Set Ω := fun n =>
    {ω | ∀ k ≤ n, ω ∈ B k}
  have hA : ∀ n, MeasurableSet (A n) := by
    intro n
    have hMeas :
        MeasurableSet (⋂ k, if k ≤ n then B k else Set.univ) := by
      apply MeasurableSet.iInter
      intro k
      split_ifs with hk
      · exact hB k
      · exact MeasurableSet.univ
    have heq : A n = ⋂ k, if k ≤ n then B k else Set.univ := by
      ext ω
      simp only [A, Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro h k
        by_cases hk : k ≤ n
        · simpa only [if_pos hk] using h k hk
        · simp [hk]
      · intro h k hk
        simpa only [if_pos hk] using h k
    rw [heq]
    exact hMeas
  have hAnti : Antitone A := by
    intro n m hnm ω hm k hk
    exact hm k (hk.trans hnm)
  have hIntersection : (⋂ n, A n) = ⋂ k, B k := by
    ext ω
    simp only [Set.mem_iInter]
    constructor
    · intro h k
      exact h k k le_rfl
    · intro h n k hk
      exact h k
  have hLim :
      (∫⁻ ω, (⋂ n, A n).indicator g ω ∂P) =
        ⨅ n, ∫⁻ ω, (A n).indicator g ω ∂P :=
    AvramDividend.Classical.chat04_antitone_grid_survival_lintegral_iInf
      A hA hAnti g hg hFin
  simpa only [hIntersection, A] using hLim
