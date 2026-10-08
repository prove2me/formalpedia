-- Prove2me | solution 1 for DSSYKScales.scrambling_separation_of_scales
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T02:44:27.704471+00:00
-- url     : https://prove2.me/submissions/99f08148-7327-4eb4-9e4e-977cf6a9f356

import Theorems.Thm_DSSYKScales_fast_scrambling_string_units
import Theorems.Thm_DSSYKScales_hyperfast_scrambling_cosmic_units

open Filter Topology DSSYKScales

theorem solution (N q : ℕ → ℕ) (lam J : ℝ) (hJ : 0 < J)
    (hlim : IsDoubleScaledLimit N q lam) :
    (∀ ts : ℝ, Tendsto (fun n => (N n : ℝ) * scramblingProbability (N n) (q n) J (ts / (q n : ℝ)))
      atTop (𝓝 (Real.exp (J * ts)))) ∧
    (∀ tc : ℝ, 0 < tc → Tendsto (fun n => 1 - scramblingProbability (N n) (q n) J tc)
      atTop (𝓝 (Real.exp (-(J * tc))))) := by
  constructor
  · intro ts
    exact fast_scrambling_string_units N q lam J hlim ts
  · intro tc htc
    exact hyperfast_scrambling_cosmic_units N q lam J hJ hlim tc htc

#print axioms solution
