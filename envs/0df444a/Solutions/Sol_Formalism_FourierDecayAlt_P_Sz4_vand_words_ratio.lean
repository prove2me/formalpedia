-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz4.vand_words_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:42:02.349003+00:00
-- url     : https://prove2.me/submissions/64e7a042-0aac-418c-a3a4-f7f3f237c33c

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_vand_ratio
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_position_ratio

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
theorem _root_.solution (c : Cfg) (de : ℕ → ℝ) (hw : IsWord c.k de) (p : ℕ) (hp : p + 1 ≤ c.k)
    (h : p + 2 ≤ c.k ∨ c.top = false) :
    Vand p (fun i => c.u de (i + 1)) = Rde p de * Vand p c.v := by
  unfold Rde
  refine vand_ratio p (fun i => c.u de (i + 1)) c.v
    (fun i j => 1 + (de j - de i) / (4 * ((j : ℝ) - (i : ℝ)))) ?_
  intro i j hi hij hj
  refine position_ratio c de hw i j hi hij (by omega) ?_
  rcases h with h | h
  · left; omega
  · right; exact h
end Formalism.FourierDecayAlt.P.Sz4
