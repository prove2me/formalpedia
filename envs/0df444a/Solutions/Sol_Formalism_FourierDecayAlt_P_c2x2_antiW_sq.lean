-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.c2x2_antiW_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:45:26.445838+00:00
-- url     : https://prove2.me/submissions/65d6a9fc-2aa4-40d1-9a99-837141ab957a

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates
import Theorems.Thm_Formalism_FourierDecayAlt_P_c2x2_antiW_mul

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
theorem _root_.solution (s : ℕ) : C2.antiW s * C2.antiW s = 1 := by
  ext i j
  rw [c2x2_antiW_mul]
  simp only [C2.antiW, Matrix.of_apply, Fin.rev_rev, Matrix.one_apply]
  by_cases h : i = j
  · simp [h]
  · rw [if_neg (fun e => h e.symm), if_neg h]
end Formalism.FourierDecayAlt.P
