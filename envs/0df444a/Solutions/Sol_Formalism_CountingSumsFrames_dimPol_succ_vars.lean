-- Prove2me | solution 1 for Formalism.CountingSumsFrames.dimPol_succ_vars
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:44:30.577558+00:00
-- url     : https://prove2.me/submissions/dcfbfa99-3bce-4f44-9710-cd450bcb6836

import Definitions.Def_Formalism_PolynomialDimension_DigitClassSize
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicLevelCountRec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution (k' b : ℕ) : dimPol (k' + 1) b * (k' + 1) = (b + k' + 1) * dimPol k' b := by
  unfold dimPol
  rw [show b + (k' + 1) = b + k' + 1 by omega]
  exact (Nat.add_one_mul_choose_eq (b + k') k').symm
end Formalism.CountingSumsFrames
