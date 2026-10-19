-- Prove2me | solution 1 for CohnElkies.lowerStripCappedPoisson_tendsto_radius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/007d52f3-af53-4fe1-9ebb-4b223979e02a

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerStripCappedPoisson_tendsto

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
    (hσbelow : -1 < σ) (hσabove : σ < 1) (s : ℝ) :
    Tendsto
      (fun n : ℕ =>
        ∫ T : ℝ,
          stripPoissonKernel σ T *
            lowerGammaBoundaryCapped ((d : ℝ) / 2)
              R (n : ℝ)
              (s - ((d : ℝ) / 2) * T))
      atTop
      (𝓝 (lowerStripPoissonMajorant ((d : ℝ) / 2)
        R σ s)) := by
  have hdreal : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hsqrt : 0 < Real.sqrt (d : ℝ) :=
    Real.sqrt_pos.mpr hdreal
  let c : ℝ := R / Real.sqrt (d : ℝ)
  have hrad : c * Real.sqrt (d : ℝ) = R := by
    try dsimp [c]
    exact div_mul_cancel₀ R hsqrt.ne'
  have h := lowerStripCappedPoisson_tendsto
    (c := c) hd hσbelow hσabove s
  simpa only [hrad] using! h
end CohnElkies
