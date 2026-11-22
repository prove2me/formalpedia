-- Prove2me | solution 1 for AvramDividend.Classical.killed_bernstein_infinite_activity_potential_ac
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T15:34:54.625764+00:00
-- url     : https://prove2.me/submissions/aa2d8de7-67d8-41d5-8ecb-627cb368d6c9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_killed_bernstein_finite_resolvent_measure_exists
import Theorems.Thm_AvramDividend_Classical_killed_bernstein_infinite_ac_resolvent_regular
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution (κ : Measure ℝ) [SFinite κ]
    (hκsupp : κ (Iic (0 : ℝ)) = 0)
    (k : ℝ) (hk : 0 < k)
    (hFin : ∀ s : ℝ, 0 < s →
      (∫⁻ t : ℝ, ENNReal.ofReal (1 - Real.exp (-(s * t))) ∂κ) ≠ ⊤)
    (hκac : κ ≪ (volume : Measure ℝ))
    (hκinf : κ (Ioc (0 : ℝ) 1) = ⊤) :
    ∃ U : Measure ℝ,
      U (Iic (0 : ℝ)) = 0 ∧
      U ≪ (volume : Measure ℝ) ∧
      (∀ x : ℝ, U {x} = 0) ∧
      U Set.univ = ENNReal.ofReal (k⁻¹) ∧
      (∀ s : ℝ, 0 < s →
        (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-(s * y))) ∂U) =
          (ENNReal.ofReal k +
            (∫⁻ t : ℝ,
              ENNReal.ofReal (1 - Real.exp (-(s * t))) ∂κ))⁻¹) := by
  obtain ⟨U, hUsupp, hMass, hLap⟩ :=
    killed_bernstein_finite_resolvent_measure_exists
      κ hκsupp k hk hFin
  obtain ⟨hIic, hAC, hAtoms⟩ :=
    killed_bernstein_infinite_ac_resolvent_regular
      κ hκsupp k hk hFin hκac hκinf U hUsupp hMass hLap
  exact ⟨U, hIic, hAC, hAtoms, hMass, hLap⟩
