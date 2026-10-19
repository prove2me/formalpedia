-- Prove2me | solution 1 for CohnElkies.stripPoissonPrimitive_centered_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:21.360486+00:00
-- url     : https://prove2.me/submissions/6d57c679-7a09-4b84-bb72-03a414ebd788

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripPoissonKernel_neg
import Theorems.Thm_CohnElkies_intervalIntegral_stripPoissonKernel

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1)
    (r s : ℝ) :
    stripPoissonPrimitive σ (-s + r) -
        stripPoissonPrimitive σ (-s - r) =
      stripPoissonPrimitive σ (s + r) -
        stripPoissonPrimitive σ (s - r) := by
  have hneg := intervalIntegral.integral_comp_neg
    (f := stripPoissonKernel σ)
    (a := s - r) (b := s + r)
  simp_rw [stripPoissonKernel_neg] at hneg
  rw [intervalIntegral_stripPoissonKernel hbelow habove,
    intervalIntegral_stripPoissonKernel hbelow habove] at hneg
  convert! hneg.symm using 1
  all_goals ring_nf
end CohnElkies
