-- Prove2me | solution 1 for CohnElkies.manuscriptQuotientRootInf_eq_critical_add_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.874095+00:00
-- url     : https://prove2.me/submissions/e16755c2-66a2-4221-b635-9b9ef163512b

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_manuscriptQuotientRootInf_div_sqrt_eq

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {d : ℕ} (hd : 0 < d) :
    sInf (manuscriptQuotientRootSet d) =
      ((Real.pi)⁻¹ + manuscriptQuotientRootError d) *
        Real.sqrt (d : ℝ) := by
  have hsqrt : 0 < Real.sqrt (d : ℝ) := by
    positivity
  have hroot :=
    (div_eq_iff hsqrt.ne').mp
      (manuscriptQuotientRootInf_div_sqrt_eq d)
  calc
    sInf (manuscriptQuotientRootSet d) =
        normalizedProgram d * Real.sqrt (d : ℝ) := hroot
    _ = ((Real.pi)⁻¹ + manuscriptQuotientRootError d) *
        Real.sqrt (d : ℝ) := by
          unfold manuscriptQuotientRootError criticalRadius
          ring
end CohnElkies
