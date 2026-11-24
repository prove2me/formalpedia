-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.admissibleWeight_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:51:33.646159+00:00
-- url     : https://prove2.me/submissions/6acc4251-ac7a-48a0-a454-e48880cc9853

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
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
variable {D : RealPlaceData k r Wp Wq} {Ξ : Mat k r → NNReal} {α : ℝ}
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {α c : ℝ} {n m n' m' : ℕ}
    {f : Mat k r → E} (h : AdmW α c n m f) (hn : n' ≤ n) (hm : m' ≤ m) : AdmW α c n' m' f :=
  ⟨fun j hj i hi => h.1 j (hj.trans hn) i (hi.trans hm), fun j hj => h.2.1 j (lt_of_lt_of_le hj hn),
    fun j hj i hi => h.2.2 j (hj.trans hn) i (lt_of_lt_of_le hi hm)⟩
end Formalism.FourierDecayAlt.P.B6
