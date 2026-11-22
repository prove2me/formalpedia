-- Prove2me | solution 1 for Formalism.CountingSumsFrames.dimPol_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:04:04.161913+00:00
-- url     : https://prove2.me/submissions/752b04d4-c17d-489e-9784-530b097a51dc

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
theorem _root_.solution (k' : ℕ) {a b : ℕ} (h : a ≤ b) : dimPol k' a ≤ dimPol k' b :=
  Nat.choose_le_choose k' (by omega)
end Formalism.CountingSumsFrames
