-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x7.dilL_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:52:55.484499+00:00
-- url     : https://prove2.me/submissions/731c201f-63ec-4b2e-a462-8c05663ffa62

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationScalesHeisenbergMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x7_aDil_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open B2x7
open Formalism.FourierDecayAlt.P.B2x7
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x7
theorem _root_.solution (t : ℝ) (x : HPar k r') :
    dilL k r' t x = (((t ^ (1 + r') : ℝ) : ℂ) • (aDil k r' t *ᵥ x.1), t ^ (2 * (1 + r')) * x.2) := by
  refine Prod.ext (funext fun i => ?_) rfl
  rw [aDil_eq]
  show (t ^ (1 + r') * dgR k r' t i) • x.1 i =
    (((t ^ (1 + r') : ℝ) : ℂ) • ((Matrix.diagonal fun i => ((dgR k r' t i : ℝ) : ℂ)) *ᵥ x.1)) i
  rw [Pi.smul_apply, Matrix.mulVec_diagonal, Complex.real_smul, smul_eq_mul]
  push_cast
  ring
end Formalism.FourierDecayAlt.P.B2x7
