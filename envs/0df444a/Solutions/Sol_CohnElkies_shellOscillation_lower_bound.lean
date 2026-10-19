-- Prove2me | solution 1 for CohnElkies.shellOscillation_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.890976+00:00
-- url     : https://prove2.me/submissions/7df8a973-cee1-4328-8f99-223286ae36e4

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_shellOscillation_eq_sinc
import Theorems.Thm_CohnElkies_sinc_explicit

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution (B T : ℝ) :
    (1 / 25 : ℝ) * min (T ^ 2) 1 ≤ shellOscillation B T := by
  rw [shellOscillation_eq_sinc]
  have hcos := Real.abs_cos_le_one ((B + 1 / 2) * T)
  have hprod :
      Real.sinc (T / 2) * Real.cos ((B + 1 / 2) * T) ≤
        |Real.sinc (T / 2)| := by
    calc
      _ ≤ |Real.sinc (T / 2) * Real.cos ((B + 1 / 2) * T)| :=
        le_abs_self _
      _ = |Real.sinc (T / 2)| * |Real.cos ((B + 1 / 2) * T)| :=
        abs_mul _ _
      _ ≤ |Real.sinc (T / 2)| := by
        nlinarith [abs_nonneg (Real.sinc (T / 2))]
  linarith [sinc_explicit T]
end CohnElkies
