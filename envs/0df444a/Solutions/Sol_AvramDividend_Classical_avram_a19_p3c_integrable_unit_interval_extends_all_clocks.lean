-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_p3c_integrable_unit_interval_extends_all_clocks
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:11:56.531738+00:00
-- url     : https://prove2.me/submissions/66d7d300-044f-463e-8283-8d1c9827b2e5

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal

/-- Any unit-interval integrable stationary-increment Lévy coordinate has
    an integrable coordinate at every deterministic nonnegative clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hUnit : ∀ t : ℝ≥0, t ≤ 1 → Integrable (X.X t) P) :
    ∀ t : ℝ≥0, Integrable (X.X t) P := by
  have hByNat : ∀ n : ℕ, ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) →
      Integrable (X.X t) P := by
    intro n
    induction n with
    | zero =>
      intro t ht
      have ht0 : t = 0 := le_zero_iff.mp (by simpa using ht)
      subst t
      exact hUnit 0 (by norm_num)
    | succ n ih =>
      intro t ht
      by_cases htn : t ≤ (n : ℝ≥0)
      · exact ih t htn
      · have hnt : (n : ℝ≥0) ≤ t := le_of_not_ge htn
        have hincle : t - (n : ℝ≥0) ≤ 1 := by
          have htreal : (t : ℝ) ≤ (n : ℝ) + 1 := by
            exact_mod_cast ht
          have hnreal : (n : ℝ) ≤ (t : ℝ) := by
            exact_mod_cast hnt
          apply NNReal.coe_le_coe.mp
          rw [NNReal.coe_sub hnt]
          norm_num
          linarith
        have hid := X.stationaryIncrements (n : ℝ≥0) t hnt
        have hinc : Integrable
            (fun ω => X.X t ω - X.X (n : ℝ≥0) ω) P :=
          (ProbabilityTheory.IdentDistrib.integrable_iff hid).2
            (hUnit _ hincle)
        have hsum := hinc.add (ih (n : ℝ≥0) le_rfl)
        have hfun :
            (fun ω => X.X t ω - X.X (n : ℝ≥0) ω) +
              X.X (n : ℝ≥0) = X.X t := by
          funext ω
          change (X.X t ω - X.X (n : ℝ≥0) ω) +
            X.X (n : ℝ≥0) ω = X.X t ω
          ring
        rw [hfun] at hsum
        exact hsum
  intro t
  obtain ⟨n, hn⟩ := exists_nat_gt (t : ℝ)
  apply hByNat n t
  exact_mod_cast (le_of_lt hn)
