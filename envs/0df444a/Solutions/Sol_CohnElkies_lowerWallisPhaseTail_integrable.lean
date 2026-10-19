-- Prove2me | solution 1 for CohnElkies.lowerWallisPhaseTail_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/dad14842-f596-429d-86f1-915119a57bae

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution :
    IntegrableOn
      (fun t : ℝ => 1 / t ^ 2 + Real.exp (-t))
      (Ioi 1) := by
  have hpower :
      IntegrableOn (fun t : ℝ => t ^ (-(2 : ℝ))) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt
      (by norm_num : (-(2 : ℝ)) < -1)
      (by norm_num : (0 : ℝ) < 1)
  have hinverse :
      IntegrableOn (fun t : ℝ => 1 / t ^ 2) (Ioi 1) := by
    apply hpower.congr_fun _ measurableSet_Ioi
    intro t ht
    have htpos : 0 < t :=
      lt_trans zero_lt_one (show 1 < t from ht)
    change t ^ (-(2 : ℝ)) = 1 / t ^ 2
    rw [Real.rpow_neg htpos.le, Real.rpow_ofNat]
    simp [one_div]
  have hexponential :
      IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 1) := by
    have h := laplaceKernel_integrable
      (a := (1 : ℝ)) zero_lt_one
    have hrestrict := h.mono_set
      (show Ioi (1 : ℝ) ⊆ Ioi 0 from
        fun t ht => by
          change 0 < t
          exact lt_trans zero_lt_one (show 1 < t from ht))
    simpa using! hrestrict
  exact hinverse.add hexponential
end CohnElkies
