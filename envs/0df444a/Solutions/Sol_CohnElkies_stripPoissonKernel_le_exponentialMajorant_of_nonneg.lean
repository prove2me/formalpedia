-- Prove2me | solution 1 for CohnElkies.stripPoissonKernel_le_exponentialMajorant_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/046dba2b-6382-4341-ad25-a9ca6c37d3c1

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripBottomMass_pos
import Theorems.Thm_CohnElkies_stripBottomMass_lt_one
import Theorems.Thm_CohnElkies_stripNormalizedPoissonKernel_eq_extension
import Theorems.Thm_CohnElkies_stripNormalizedPoissonExtension_le_majorant

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Bornology Complex Filter Function MeasureTheory Metric Set
open scoped Filter FourierTransform Real SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution
    {σ : ℝ} (hσ : 0 ≤ σ) (hσone : σ < 1)
    (T : ℝ) :
    stripPoissonKernel σ T ≤
      stripPoissonExponentialMajorant T := by
  have hbelow : -1 < σ := by linarith
  have hmass := stripBottomMass_pos hσone
  have hmassone :=
    (stripBottomMass_lt_one hbelow).le
  have hext :=
    stripNormalizedPoissonExtension_le_majorant
      hσ hσone.le T
  have hreconstruct :
      stripPoissonKernel σ T =
        stripBottomMass σ *
          stripNormalizedPoissonExtension σ T := by
    rw [← stripNormalizedPoissonKernel_eq_extension
      hbelow hσone T]
    unfold stripNormalizedPoissonKernel
    field_simp [hmass.ne']
  rw [hreconstruct]
  calc
    stripBottomMass σ *
        stripNormalizedPoissonExtension σ T ≤
      1 * stripNormalizedPoissonExtension σ T :=
        mul_le_mul_of_nonneg_right hmassone hext.1
    _ = stripNormalizedPoissonExtension σ T := one_mul _
    _ ≤ stripPoissonExponentialMajorant T := hext.2
end CohnElkies
