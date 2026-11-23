-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WordMonicExtraction.natDegree_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:37:22.347868+00:00
-- url     : https://prove2.me/submissions/43822b54-7f69-4b67-a1e9-d2985d114ef4

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordMonicExtraction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WordMonicExtraction
open Finset Polynomial Formalism.FourierDecayAlt.F7
namespace Formalism.FourierDecayAlt.P.WordMonicExtraction
theorem _root_.solution (h : ℂ) (i j : ℕ) :
    ((X : ℂ[X]) ^ i * (X + C h) ^ j).natDegree = i + j := by
  rw [(Polynomial.monic_X_pow i).natDegree_mul ((Polynomial.monic_X_add_C h).pow j),
    Polynomial.natDegree_X_pow, (Polynomial.monic_X_add_C h).natDegree_pow, Polynomial.natDegree_X_add_C,
    mul_one]
end Formalism.FourierDecayAlt.P.WordMonicExtraction
