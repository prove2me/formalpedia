-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.lie_rsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:53:54.448513+00:00
-- url     : https://prove2.me/submissions/5a6cd312-af3c-4c84-812f-f897182f5ab5

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
theorem _root_.solution {X : Mat k r} (hX : inLie k r X) (t : ℝ) : inLie k r ((t : ℂ) • X) := by
  have hX' : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  have h : star (t : ℂ) = (t : ℂ) := by simp
  show ((t : ℂ) • X)ᴴ * Hpk k r + Hpk k r * ((t : ℂ) • X) = 0
  rw [Matrix.conjTranspose_smul, h, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX', smul_zero]
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
