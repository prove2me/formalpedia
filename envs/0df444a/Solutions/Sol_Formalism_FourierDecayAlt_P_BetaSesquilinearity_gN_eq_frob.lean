-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_eq_frob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:34:13.534691+00:00
-- url     : https://prove2.me/submissions/0bee6fd1-f935-4c01-a0d1-4e0db6b78770

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
attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup Matrix.frobeniusNormedAddCommGroup
  Matrix.frobeniusNormedSpace Matrix.frobeniusNormedRing
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
theorem _root_.solution {k r : ℕ} (g : Mat k r) : gN g = ‖g‖ := by
  unfold gN
  rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  simp only [Complex.normSq_eq_norm_sq, Real.rpow_two]
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
