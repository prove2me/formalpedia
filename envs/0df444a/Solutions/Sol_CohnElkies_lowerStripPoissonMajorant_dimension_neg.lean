-- Prove2me | solution 1 for CohnElkies.lowerStripPoissonMajorant_dimension_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/db395045-99c7-41a4-9a82-fdce405de9b4

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripPoissonKernel_neg
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_dimension_neg

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
    {d : ℕ} (hd : 0 < d) (R σ s : ℝ) :
    lowerStripPoissonMajorant ((d : ℝ) / 2) R σ (-s) =
      lowerStripPoissonMajorant ((d : ℝ) / 2) R σ s := by
  have hℓ : 0 < (d : ℝ) / 2 := by positivity
  let f : ℝ → ℝ := fun T =>
    stripPoissonKernel σ T *
      lowerGammaBoundaryLog ((d : ℝ) / 2) R
        (s - ((d : ℝ) / 2) * T)
  unfold lowerStripPoissonMajorant
  calc
    (∫ T : ℝ,
      stripPoissonKernel σ T *
        lowerGammaBoundaryLog ((d : ℝ) / 2) R
          (-s - ((d : ℝ) / 2) * T)) =
      ∫ T : ℝ, f (-T) := by
        apply integral_congr_ae
        filter_upwards
          [Measure.ae_ne (volume : Measure ℝ)
            (-s / ((d : ℝ) / 2))]
          with T hT
        have hy : s + ((d : ℝ) / 2) * T ≠ 0 := by
          intro hzero
          apply hT
          apply (eq_div_iff hℓ.ne').2
          nlinarith
        try dsimp [f]
        rw [stripPoissonKernel_neg]
        have harg :
            -s - ((d : ℝ) / 2) * T =
              -(s + ((d : ℝ) / 2) * T) := by
          ring
        rw [harg, lowerGammaBoundaryLog_dimension_neg R hy]
        congr 1
        ring_nf
    _ = ∫ T : ℝ, f T :=
      integral_neg_eq_self f volume
    _ = ∫ T : ℝ,
      stripPoissonKernel σ T *
        lowerGammaBoundaryLog ((d : ℝ) / 2) R
          (s - ((d : ℝ) / 2) * T) := by
      rfl
end CohnElkies
