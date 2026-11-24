-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.c2x2_mul_antiW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:39:32.893086+00:00
-- url     : https://prove2.me/submissions/b19fd7e3-1709-43dd-9a56-11d5055d4934

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x2
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution {s : ℕ} (M : Matrix (Fin s) (Fin s) ℂ) (i j : Fin s) :
    (M * C2.antiW s) i j = M i j.rev := by
  simp only [C2.antiW, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.sum_eq_single j.rev]
  · simp
  · intro k _ hk
    rw [if_neg, mul_zero]
    intro e; apply hk; rw [e, Fin.rev_rev]
  · simp
end Formalism.FourierDecayAlt.P
