-- Prove2me | solution 1 for AvramDividend.Classical.excursion_rescale_normalized_weak_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T23:11:58.027989+00:00
-- url     : https://prove2.me/submissions/16d0c934-952a-4a98-938a-498e56cb72ea

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology

/-!
Fixed-mass rescaling transfers weak convergence of the
normalised probability measures to weak convergence of the
original finite measures, retaining the common mass.
-/
theorem solution
    (ν : ℕ → FiniteMeasure ℝ) (c : NNReal)
    (hmass : ∀ n : ℕ, (ν n).mass = c)
    (P : ProbabilityMeasure ℝ) (φ : ℕ → ℕ)
    (hlim : Tendsto (fun n : ℕ => (ν (φ n)).normalize)
      atTop (𝓝 P)) :
    Tendsto (fun n : ℕ => ν (φ n)) atTop
      (𝓝 (c • P.toFiniteMeasure)) := by
  have hp : Tendsto
      (fun n : ℕ => (ν (φ n)).normalize.toFiniteMeasure)
      atTop (𝓝 P.toFiniteMeasure) :=
    ProbabilityMeasure.toFiniteMeasure_continuous.tendsto P |>.comp hlim
  have hs : Tendsto
      (fun n : ℕ => c • (ν (φ n)).normalize.toFiniteMeasure)
      atTop (𝓝 (c • P.toFiniteMeasure)) :=
    (continuous_const_smul c).tendsto P.toFiniteMeasure |>.comp hp
  have heq : (fun n : ℕ => ν (φ n)) =
      (fun n : ℕ => c • (ν (φ n)).normalize.toFiniteMeasure) := by
    funext n
    calc
      ν (φ n) =
          (ν (φ n)).mass • (ν (φ n)).normalize.toFiniteMeasure :=
        FiniteMeasure.self_eq_mass_smul_normalize (ν (φ n))
      _ = c • (ν (φ n)).normalize.toFiniteMeasure := by
        rw [hmass (φ n)]
  rw [heq]
  exact hs
