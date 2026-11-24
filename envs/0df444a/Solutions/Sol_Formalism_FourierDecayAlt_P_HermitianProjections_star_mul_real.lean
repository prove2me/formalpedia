-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianProjections.star_mul_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:22:43.479844+00:00
-- url     : https://prove2.me/submissions/e3528ad5-2b3d-4dc7-a1a1-ad421d6d34ab

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormBasics

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianProjections
namespace Formalism.FourierDecayAlt.P.HermitianProjections
theorem _root_.solution (a : ℝ) (x : ℂ) : (star x * ((a : ℂ) * x)).re = a * Complex.normSq x := by
  simp [Complex.mul_re, Complex.normSq_apply]
  try ring
end Formalism.FourierDecayAlt.P.HermitianProjections
