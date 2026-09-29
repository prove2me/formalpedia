-- Prove2me | solution 1 for FamousTheorems.cauchy_mean_value_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T21:37:11.743666+00:00
-- url     : https://prove2.me/submissions/ce524259-afda-4597-bd1b-9c80d4d256c2

import Mathlib

theorem solution {f f' g g' : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hfc : ContinuousOn f (Set.Icc a b))
    (hff' : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x) (hgc : ContinuousOn g (Set.Icc a b))
    (hgg' : ∀ x ∈ Set.Ioo a b, HasDerivAt g (g' x) x) :
    ∃ c ∈ Set.Ioo a b, (g b - g a) * f' c = (f b - f a) * g' c := by
  exact exists_ratio_hasDerivAt_eq_ratio_slope f f' hab hfc hff' g g' hgc hgg'
