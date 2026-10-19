-- Prove2me | solution 1 for CohnElkies.tendsto_log_factorialStirlingSequence_div_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/cfa3e56b-4dbb-48c9-aea6-ce2c34ffcfc1

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_tendsto_log_factorialStirlingSequence

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
      (fun k : ℕ => Real.log (Stirling.stirlingSeq k) / (k : ℝ))
      atTop (nhds 0) := by
  convert! tendsto_log_factorialStirlingSequence.mul
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)) using 1;
    simp
end CohnElkies
