-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz4.pair_small
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:39:40.42875+00:00
-- url     : https://prove2.me/submissions/c5b289c4-646b-4d1e-a120-3e11570c6af1

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
theorem _root_.solution (de : ℕ → ℝ) (h01 : ∀ i, de i = 0 ∨ de i = 1) (i j : ℕ) (hij : i < j) :
    |(de j - de i) / (4 * ((j : ℝ) - (i : ℝ)))| ≤ 1 / 4 := by
  have h1 : (1 : ℝ) ≤ (j : ℝ) - i := by
    have : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
    linarith
  rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < 4 * ((j : ℝ) - i)), div_le_iff₀ (by linarith)]
  have h2 : |de j - de i| ≤ 1 := by
    rcases h01 j with a | a <;> rcases h01 i with b | b <;> rw [a, b] <;> norm_num
  linarith
end Formalism.FourierDecayAlt.P.Sz4
