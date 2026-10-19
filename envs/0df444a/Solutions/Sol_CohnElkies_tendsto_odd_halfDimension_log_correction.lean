-- Prove2me | solution 1 for CohnElkies.tendsto_odd_halfDimension_log_correction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/179277ab-99fc-4bf4-905d-b80471c5d09a

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_tendsto_log_nat_div_oddDimension

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Nat Topology
namespace CohnElkies
theorem _root_.solution :
    Tendsto
      (fun k : ℕ =>
        ((k : ℝ) / (2 * (k : ℝ) + 1) - (1 / 2 : ℝ)) *
          Real.log (k : ℝ))
      atTop (nhds 0) := by
  have hscaled :=
    tendsto_log_nat_div_oddDimension.const_mul (-1 / 2 : ℝ)
  have hlimit :
      Tendsto
        (fun k : ℕ =>
          (-1 / 2 : ℝ) *
            (Real.log (k : ℝ) / (2 * (k : ℝ) + 1)))
        atTop (nhds 0) := by
    convert! hscaled using 1; norm_num
  refine hlimit.congr' (Filter.Eventually.of_forall ?_)
  intro k
  have hodd : 2 * (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring
end CohnElkies
