-- Prove2me | solution 1 for CohnElkies.lowerGammaScaledCappedClipped_poisson_convolution_max
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/e7d54bed-f6a4-40ab-a8f8-0e1321d7fc11

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_even_antitone_poisson_convolution_max
import Theorems.Thm_CohnElkies_lowerGammaScaledCappedClipped_continuous
import Theorems.Thm_CohnElkies_lowerGammaScaledCappedClipped_neg
import Theorems.Thm_CohnElkies_lowerGammaScaledCappedClipped_antitoneOn
import Theorems.Thm_CohnElkies_lowerGammaScaledCappedClipped_support
import Theorems.Thm_CohnElkies_lowerGammaScaledCappedClipped_integrable

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
    {d : ℕ} (hd : 2 ≤ d) {c D n σ : ℝ}
    (hc : 0 < c) (hn : 0 ≤ n)
    (hbelow : -1 < σ) (habove : σ < 1) (s : ℝ) :
    (∫ Y : ℝ, stripPoissonKernel σ (s - Y) *
      lowerGammaScaledCappedClipped d c D n Y) ≤
      ∫ Y : ℝ, stripPoissonKernel σ (0 - Y) *
        lowerGammaScaledCappedClipped d c D n Y := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  exact even_antitone_poisson_convolution_max
    hbelow habove
    (lowerGammaScaledCappedClipped_integrable hd hc hn)
    (lowerGammaScaledCappedClipped_continuous
      hdpos c D n).measurable
    (fun Y => le_max_right _ _)
    (lowerGammaScaledCappedClipped_neg d c D n)
    (lowerGammaScaledCappedClipped_antitoneOn d c D n)
    (lowerGammaScaledCappedClipped_support hd hc hn)
    s
end CohnElkies
