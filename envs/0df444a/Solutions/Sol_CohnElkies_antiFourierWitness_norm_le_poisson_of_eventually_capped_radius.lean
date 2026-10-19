-- Prove2me | solution 1 for CohnElkies.antiFourierWitness_norm_le_poisson_of_eventually_capped_radius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/9e69e22f-ad59-42e4-b19f-ba99b90621df

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerStripCappedPoisson_tendsto_radius

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology
namespace CohnElkies
theorem _root_.solution
    {d : ℕ} (hd : 0 < d) {R σ : ℝ}
    (w : AntiFourierWitness d R)
    (hσbelow : -1 < σ) (hσabove : σ < 1) (s : ℝ)
    (hcapped : ∀ᶠ n : ℕ in atTop,
      ‖normalizedRadialMellinStrip hd w.function R
        ((s : ℂ) + Complex.I *
          (((σ * ((d : ℝ) / 2) : ℝ) : ℂ)))‖ ≤
        Real.exp
          (∫ T : ℝ,
            stripPoissonKernel σ T *
              lowerGammaBoundaryCapped ((d : ℝ) / 2)
                R (n : ℝ)
                  (s - ((d : ℝ) / 2) * T))) :
      ‖normalizedRadialMellinStrip hd w.function R
        ((s : ℂ) + Complex.I *
          (((σ * ((d : ℝ) / 2) : ℝ) : ℂ)))‖ ≤
        Real.exp
          (lowerStripPoissonMajorant ((d : ℝ) / 2)
            R σ s) := by
  have hlimit := lowerStripCappedPoisson_tendsto_radius
    (R := R) hd hσbelow hσabove s
  have hexp :=
    Real.continuous_exp.continuousAt.tendsto.comp hlimit
  exact le_of_tendsto_of_tendsto
    tendsto_const_nhds hexp hcapped
end CohnElkies
