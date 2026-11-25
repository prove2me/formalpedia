-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.positionDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:50:53.163404+00:00
-- url     : https://prove2.me/submissions/65d43713-eb30-482a-8119-178b7365e8ce

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VandermondeRatioHarmonic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Sz.PositionDiff := by
  intro c de hc hw i i' hi hii' hi'k hor
  have h1 : c.u de (i + 1) = c.v i - 1 / 2 - de i * c.Del := by
    unfold Cfg.u
    rw [if_neg (by omega), if_neg (by omega)]; simp
  rw [h1]
  by_cases hlast : i' + 1 = c.k
  · have htop : c.top = false := by
      rcases hor with h | h
      · omega
      · exact h
    have h2 : c.u de (i' + 1) = c.vlast - 1 / 2 := by
      unfold Cfg.u
      rw [if_neg (by omega), if_pos hlast]
      simp [Cfg.ulast, htop]
    have hde : de i' = 0 := by
      have : i' = c.k - 1 := by omega
      rw [this]; exact hw.2
    have hkR : (i' : ℝ) + 1 = (c.k : ℝ) := by exact_mod_cast hlast
    rw [h2, hde]; unfold Cfg.v; rw [← hkR]; ring
  · have h2 : c.u de (i' + 1) = c.v i' - 1 / 2 - de i' * c.Del := by
      unfold Cfg.u
      rw [if_neg (by omega), if_neg hlast]; simp
    rw [h2]; unfold Cfg.v; ring
end Formalism.FourierDecayAlt.P
