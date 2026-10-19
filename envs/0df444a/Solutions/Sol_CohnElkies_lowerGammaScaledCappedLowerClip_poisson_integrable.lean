-- Prove2me | solution 1 for CohnElkies.lowerGammaScaledCappedLowerClip_poisson_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/f307ab6e-ba7d-4293-afd4-a4d6d925599a

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripPoissonKernel_pos
import Theorems.Thm_CohnElkies_stripPoissonKernel_integrable
import Theorems.Thm_CohnElkies_lowerGammaScaledCapped_poisson_product_integrable

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
    {d : ℕ} (hd : 0 < d) {c D n σ : ℝ}
    (hbelow : -1 < σ) (habove : σ < 1) (s : ℝ) :
    Integrable (fun Y : ℝ =>
      stripPoissonKernel σ (s - Y) *
        lowerGammaScaledCappedLowerClip d c D n Y) := by
  have hbase := lowerGammaScaledCapped_poisson_product_integrable
    hd (R := c * Real.sqrt d) (D := D) hbelow habove s
  have hk := (stripPoissonKernel_integrable hbelow habove).comp_sub_left s
  have hconstant := hk.const_mul (-n)
  have hmax := hbase.sup hconstant
  convert! hmax using 1
  ext Y
  change
    stripPoissonKernel σ (s - Y) *
        max
          (lowerGammaBoundaryCapped ((d : ℝ) / 2)
            (c * Real.sqrt d) D (((d : ℝ) / 2) * Y))
          (-n) =
      max
        (stripPoissonKernel σ (s - Y) *
          lowerGammaBoundaryCapped ((d : ℝ) / 2)
            (c * Real.sqrt d) D (((d : ℝ) / 2) * Y))
        (-n * stripPoissonKernel σ (s - Y))
  rw [mul_max_of_nonneg _ _
    (stripPoissonKernel_pos hbelow habove (s - Y)).le]
  ring_nf
end CohnElkies
