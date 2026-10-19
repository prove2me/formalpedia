-- Prove2me | solution 1 for CohnElkies.norm_saddleShellExponential_eq_exp_neg_damping
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.275309+00:00
-- url     : https://prove2.me/submissions/9710a76e-6eee-414a-9b4f-2a822bfcf4e0

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleShellPhase_damping_identity

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
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (ℓ T u : ℝ) :
    ‖Complex.exp
      ((ℓ : ℂ) * mellinShellPhase ε
        ((T : ℂ) + Complex.I * (u : ℂ)))‖ =
      Real.exp (ℓ * realHyperbolicShellPhase ε u) *
        Real.exp
          (-(positiveShellDamping ε ℓ (u - 1) T -
            upperShortShellDamping ε ℓ (u - 1) T)) := by
  rw [Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  have hphase := saddleShellPhase_damping_identity
    hε horder ℓ T u
  rw [← Real.exp_add]
  congr 1
  linarith
end CohnElkies
