-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.lie_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:00:40.737809+00:00
-- url     : https://prove2.me/submissions/bbcc902c-6645-4781-89c0-339240085760

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BetaSesquilinearity
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
open scoped ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
theorem _root_.solution {X : Mat k r} (hX : inLie k r X) : inLie k r (-X) := by
  have hX' : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  show (-X)ᴴ * Hpk k r + Hpk k r * (-X) = 0
  rw [Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add, hX', neg_zero]
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
