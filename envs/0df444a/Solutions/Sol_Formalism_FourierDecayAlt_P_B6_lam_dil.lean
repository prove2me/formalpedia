-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.lam_dil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:06:02.026474+00:00
-- url     : https://prove2.me/submissions/bcfdb0c5-5e4f-42d4-8801-70fd899350ab

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne

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
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution (hN : DilN) (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) {x y : ℝ} (hx : 0 < x)
    (hy : 0 < y) :
    lam k r D.z (Matrix.of (dilation₂ (x, y) p).1.2) = x * lam k r D.z (Matrix.of p.1.2) ∧
    lam k r D.z' (Matrix.of (dilation₂ (x, y) p).2.2) = y * lam k r D.z' (Matrix.of p.2.2) :=
  ⟨(hN k r D.z x hx.ne' D.z_mem _ hp.2.1).2.2, (hN k r D.z' y hy.ne' D.z'_mem _ hp.2.2.2).2.2⟩
end Formalism.FourierDecayAlt.P.B6
