-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz4.u_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:15:08.742324+00:00
-- url     : https://prove2.me/submissions/395f11f1-3f69-4a97-8a21-1fcbbfeab802

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz4
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz4
theorem _root_.solution (c : Cfg) (de : ℕ → ℝ) (hw : IsWord c.k de) (i : ℕ) (hi : 1 ≤ i)
    (_hik : i + 1 ≤ c.k) (h : i + 2 ≤ c.k ∨ c.top = false) :
    c.u de (i + 1) = c.v i - 1 / 2 - de i * c.Del := by
  have h1 : i + 1 ≠ 1 := by omega
  by_cases hlast : i + 1 = c.k
  · have ht : c.top = false := by
      rcases h with h | h
      · omega
      · exact h
    have hi' : i = c.k - 1 := by omega
    have hde : de i = 0 := by rw [hi']; exact hw.2
    have hiR : (i : ℝ) + 1 = c.k := by exact_mod_cast hlast
    unfold Cfg.u; rw [if_neg h1, if_pos hlast, hde]
    unfold Cfg.ulast Cfg.v; rw [← hiR]; simp [ht]
  · unfold Cfg.u; rw [if_neg h1, if_neg hlast]; simp
end Formalism.FourierDecayAlt.P.Sz4
