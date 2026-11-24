-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FixedPointsGramVector.mem_Uperp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:32:15.537666+00:00
-- url     : https://prove2.me/submissions/b00d1e95-9396-4230-acc7-c04f8208ec9f

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FixedFrameProperty
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormBasics
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FixedPointsGramVector
import Theorems.Thm_Formalism_FourierDecayAlt_P_FixedPointsGramVector_of_star_gramVec

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
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.FixedPointsGramVector
open C2x5 C2x6 C2x7 HermitianProjections
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.FixedPointsGramVector
theorem _root_.solution (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (v : Fin (2 * r + k + 1) → ℂ) :
    v ∈ C2.Uperp k r z z' γ ↔ ((gnB k r z z' γ)ᴴ * Hpk k r) *ᵥ v = 0 := by
  simp only [C2.Uperp, LinearMap.mem_ker, Matrix.mulVecLin_apply, of_star_gramVec]
end Formalism.FourierDecayAlt.P.FixedPointsGramVector
