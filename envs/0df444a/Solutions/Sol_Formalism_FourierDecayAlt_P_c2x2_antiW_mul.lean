-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.c2x2_antiW_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:25:54.850794+00:00
-- url     : https://prove2.me/submissions/7d301634-d85b-4bd2-ac6e-f42a44ecf70c

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
    (C2.antiW s * M) i j = M i.rev j := by
  simp only [C2.antiW, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.sum_eq_single i.rev]
  · simp
  · intro k _ hk; rw [if_neg hk, zero_mul]
  · simp
end Formalism.FourierDecayAlt.P
