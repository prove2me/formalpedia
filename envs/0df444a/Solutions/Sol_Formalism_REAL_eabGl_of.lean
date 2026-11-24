-- Prove2me | solution 1 for Formalism.REAL.eabGl_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:13:30.662127+00:00
-- url     : https://prove2.me/submissions/413bcea9-4301-43a4-ac66-96b183b28ca7

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Theorems.Thm_Formalism_REAL_complexified_derivative_sub
import Theorems.Thm_Formalism_REAL_complexified_derivative_zero
import Theorems.Thm_Formalism_REAL_complexified_derivative_commutator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open Formalism Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.REAL
theorem _root_.solution (hc : CpartMem) (hl : RdLin) (hb : RdBracket) (hs : RdSmooth) : EabGl := by
  intro n ε f a b c d g hf hg
  unfold Eab
  rw [complexified_derivative_commutator hc hl hb hs ε f _ _ g hf hg]
  have hm : Matrix.single a b (1 : ℂ) * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1 =
      (if b = c then Matrix.single a d 1 else 0) - (if d = a then Matrix.single c b 1 else 0) := by
    by_cases h1 : b = c <;> by_cases h2 : d = a
    · subst h1; subst h2; simp
    · subst h1; simp [h2]
    · subst h2; simp [h1]
    · simp [h1, h2]
  rw [hm, complexified_derivative_sub hc hl hf hg]
  split_ifs <;> simp [complexified_derivative_zero]
end Formalism.REAL
