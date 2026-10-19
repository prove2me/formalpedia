-- Prove2me | solution 1 for CohnElkies.lowerStripCappedPoisson_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/a10f7aef-e264-4347-ac98-4800c3eae834

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerGammaScaledCapped_poisson_tendsto
import Theorems.Thm_CohnElkies_lowerStripPoissonMajorant_scaled_convolution

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
    {d : ℕ} (hd : 0 < d) {c σ : ℝ}
    (hσbelow : -1 < σ) (hσabove : σ < 1) (s : ℝ) :
    Tendsto
      (fun n : ℕ =>
        ∫ T : ℝ,
          stripPoissonKernel σ T *
            lowerGammaBoundaryCapped ((d : ℝ) / 2)
              (c * Real.sqrt d) (n : ℝ)
              (s - ((d : ℝ) / 2) * T))
      atTop
      (𝓝 (lowerStripPoissonMajorant ((d : ℝ) / 2)
        (c * Real.sqrt d) σ s)) := by
  have hℓ : 0 < (d : ℝ) / 2 := by positivity
  rw [lowerStripPoissonMajorant_scaled_convolution
    hℓ (c * Real.sqrt d) σ s]
  have h := lowerGammaScaledCapped_poisson_tendsto
    (c := c) hd hσbelow hσabove
      (s / ((d : ℝ) / 2))
  convert! h using 1
  ext n
  let f : ℝ → ℝ := fun Y =>
    stripPoissonKernel σ (s / ((d : ℝ) / 2) - Y) *
      lowerGammaBoundaryCapped ((d : ℝ) / 2)
        (c * Real.sqrt d) (n : ℝ)
          (((d : ℝ) / 2) * Y)
  calc
    (∫ T : ℝ,
      stripPoissonKernel σ T *
        lowerGammaBoundaryCapped ((d : ℝ) / 2)
          (c * Real.sqrt d) (n : ℝ)
            (s - ((d : ℝ) / 2) * T)) =
        ∫ T : ℝ, f (s / ((d : ℝ) / 2) - T) := by
          apply integral_congr_ae
          filter_upwards [] with T
          try dsimp [f]
          have hkernel :
              s / ((d : ℝ) / 2) -
                (s / ((d : ℝ) / 2) - T) = T := by
            ring
          have harg :
              ((d : ℝ) / 2) *
                (s / ((d : ℝ) / 2) - T) =
                  s - ((d : ℝ) / 2) * T := by
            field_simp [hℓ.ne']
          rw [hkernel, harg]
    _ = ∫ Y : ℝ, f Y :=
      integral_sub_left_eq_self f volume
        (s / ((d : ℝ) / 2))
    _ = ∫ Y : ℝ,
      stripPoissonKernel σ
        (s / ((d : ℝ) / 2) - Y) *
          lowerGammaBoundaryCapped ((d : ℝ) / 2)
            (c * Real.sqrt d) (n : ℝ)
              (((d : ℝ) / 2) * Y) := by
      rfl
end CohnElkies
