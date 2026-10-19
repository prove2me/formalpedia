-- Prove2me | solution 1 for CohnElkies.tendsto_saddleGammaArgument_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.057836+00:00
-- url     : https://prove2.me/submissions/16ab486d-37e7-4ff4-a395-9d0ca7d8788e

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution
    {d : ℕ} (hd : 0 < d) :
    Tendsto
      (fun u : ℝ =>
        ((d : ℝ) / 2) * (1 + u) / 2)
      atTop atTop := by
  have hdreal : 0 < (d : ℝ) := by
    exact_mod_cast hd
  have hslope : 0 < (d : ℝ) / 4 := by positivity
  have hlinear := tendsto_id.const_mul_atTop hslope
  have h := hlinear.atTop_add
    (tendsto_const_nhds (x := (d : ℝ) / 4))
  convert! h using 1
  funext u
  simp only [id_eq]
  ring
end CohnElkies
