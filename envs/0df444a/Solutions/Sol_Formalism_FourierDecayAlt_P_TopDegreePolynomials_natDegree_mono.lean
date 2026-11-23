-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TopDegreePolynomials.natDegree_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:34:26.562743+00:00
-- url     : https://prove2.me/submissions/7fcd7bad-9ab1-457d-9209-ac58b4228f9b

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopDegreePolynomials

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TopDegreePolynomials
open Finset Polynomial Formalism.FourierDecayAlt.F7
namespace Formalism.FourierDecayAlt.P.TopDegreePolynomials
theorem _root_.solution (h : ℂ) (i j : ℕ) :
    ((X : ℂ[X]) ^ i * (X + C h) ^ j).natDegree = i + j := by
  rw [Monic.natDegree_mul (monic_X_pow i) ((monic_X_add_C h).pow j), natDegree_X_pow,
    Monic.natDegree_pow (monic_X_add_C h), natDegree_X_add_C, mul_one]
end Formalism.FourierDecayAlt.P.TopDegreePolynomials
