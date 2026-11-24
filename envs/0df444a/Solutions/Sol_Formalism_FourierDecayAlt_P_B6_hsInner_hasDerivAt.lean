-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.hsInner_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:06:08.235797+00:00
-- url     : https://prove2.me/submissions/1af19978-c538-4a64-9ed5-4511cb5eac41

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_hilbert_schmidt_inner_basis_sum

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution {u v : ℝ → (Wq →L[ℂ] Wp)} {u' v' : Wq →L[ℂ] Wp} {y : ℝ} (hu : HasDerivAt u u' y)
    (hv : HasDerivAt v v' y) :
    HasDerivAt (fun s => hsInner (u s) (v s)) (hsInner u' (v y) + hsInner (u y) v') y := by
  simp only [hilbert_schmidt_inner_basis_sum, ← Finset.sum_add_distrib]
  refine HasDerivAt.fun_sum fun i _ => ?_
  have h1 : HasDerivAt (fun s => u s (stdOrthonormalBasis ℂ Wq i)) (u' (stdOrthonormalBasis ℂ Wq i)) y := by
    exact ((ContinuousLinearMap.apply ℂ Wp (stdOrthonormalBasis ℂ Wq i)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt y hu
  have h2 : HasDerivAt (fun s => v s (stdOrthonormalBasis ℂ Wq i)) (v' (stdOrthonormalBasis ℂ Wq i)) y := by
    exact ((ContinuousLinearMap.apply ℂ Wp (stdOrthonormalBasis ℂ Wq i)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt y hv
  exact h2.inner ℂ h1
end Formalism.FourierDecayAlt.P.B6
