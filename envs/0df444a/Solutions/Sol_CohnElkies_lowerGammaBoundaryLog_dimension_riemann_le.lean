-- Prove2me | solution 1 for CohnElkies.lowerGammaBoundaryLog_dimension_riemann_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/984cfbf8-db68-4b50-95e0-fe6a6ab782f2

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_integer_riemann_le
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_halfInteger_riemann_le

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
    {d : ℕ} (hd : 2 ≤ d) {R T : ℝ}
    (hR : 0 < R) (hT : T ≠ 0) :
    lowerGammaBoundaryLog ((d : ℝ) / 2) R
        (((d : ℝ) / 2) * T) ≤
      ((d : ℝ) / 2) *
        (Real.log (Real.pi * R ^ 2 / ((d : ℝ) / 2)) +
          1 + lowerEndpointPhase T) +
        lowerRiemannErrorMajorant T := by
  rcases d.even_or_odd with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have hk : 0 < k := by omega
    have hq : ((↑(k + k) : ℝ) / 2) = (k : ℝ) := by
      push_cast
      ring
    rw [hq]
    exact lowerGammaBoundaryLog_integer_riemann_le
      hk hR hT
  · have hk : 0 < k := by omega
    have hq : ((↑(2 * k + 1) : ℝ) / 2) =
        (k : ℝ) + 1 / 2 := by
      push_cast
      ring
    rw [hq]
    apply lowerGammaBoundaryLog_halfInteger_riemann_le
      k rfl
    · have hkre : 1 ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
    · exact hR
    · exact hT
end CohnElkies
