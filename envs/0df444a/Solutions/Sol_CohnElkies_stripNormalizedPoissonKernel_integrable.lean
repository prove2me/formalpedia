-- Prove2me | solution 1 for CohnElkies.stripNormalizedPoissonKernel_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/6d6296de-cde0-41e5-83e8-31c400a7412b

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripPoissonKernel_integrable

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
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1) :
    Integrable (stripNormalizedPoissonKernel σ) := by
  unfold stripNormalizedPoissonKernel
  exact (stripPoissonKernel_integrable hbelow habove).div_const _
end CohnElkies
