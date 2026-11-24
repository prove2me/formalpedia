-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WittOrthonormalBasis.mul_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:05:47.697829+00:00
-- url     : https://prove2.me/submissions/84374950-7ba7-42dd-85c5-224f4ecac4a4

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagGramRestriction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WittOrthonormalBasis

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
open Formalism.FourierDecayAlt.P.WittOrthonormalBasis
open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector FlagGramRestriction
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.WittOrthonormalBasis
theorem _root_.solution {m κ μ : Type*} [Fintype κ] (M : Matrix m κ ℂ) (N : Matrix κ μ ℂ) (i : m) (j : μ) :
    (M * N) i j = (M *ᵥ fun a => N a j) i := by
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
end Formalism.FourierDecayAlt.P.WittOrthonormalBasis
