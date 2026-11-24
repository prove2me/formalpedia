-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GeometricRayBounds.exp_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:17:07.538044+00:00
-- url     : https://prove2.me/submissions/db59892a-67ba-4f1e-928a-e511dc83ed79

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AveragingVanishes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GeometricRayBounds
namespace Formalism.FourierDecayAlt.P.GeometricRayBounds
theorem _root_.solution {x : ℝ} (h0 : x ≠ 0) (h1 : |x| < 2 * Real.pi) :
    Complex.exp (Complex.I * (x : ℂ)) ≠ 1 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h
  have h2 := congrArg Complex.im hn
  simp at h2
  have hx : x = n * (2 * Real.pi) := by linarith
  have hpi := Real.pi_pos
  rw [hx, abs_lt] at h1
  rcases lt_trichotomy n 0 with hn0 | hn0 | hn0
  · have h3 : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hn0
    nlinarith
  · subst hn0
    simp at hx
    exact h0 hx
  · have h3 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
    nlinarith
end Formalism.FourierDecayAlt.P.GeometricRayBounds
