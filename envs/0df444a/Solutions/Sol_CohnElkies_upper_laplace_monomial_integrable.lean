-- Prove2me | solution 1 for CohnElkies.upper_laplace_monomial_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/45376633-bd15-4a3d-b14a-43930381411c

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {η : ℝ} (hη : 0 < η) (k : ℕ) :
    IntegrableOn
      (fun a : ℝ => a ^ k * Real.exp (-η * a))
      (Set.Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (s := (k : ℝ)) (b := η)
    (by exact_mod_cast (show (-(1 : ℤ) < (k : ℤ)) by omega))
    (by norm_num) hη
  apply h.congr_fun _ measurableSet_Ioi
  intro a ha
  simp [Real.rpow_natCast]
end CohnElkies
