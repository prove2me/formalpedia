-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.continuousOn_conj_by_dilation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:05:59.116794+00:00
-- url     : https://prove2.me/submissions/c9b20908-a299-4aff-b5bd-286c294a06c8

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_aDil_continuousOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_aDil_inv_continuousOn

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
theorem _root_.solution (k r : ℕ) (φ : SS k r × (ℝ × ℝ) → Mt k r) (hφ : Continuous φ)
    (ψ : SS k r × (ℝ × ℝ) → ℝ) (hψ : Continuous ψ) (hpos : ∀ q ∈ (Set.univ : Set (SS k r)) ×ˢ Quad, 0 < ψ q) :
    ContinuousOn (fun q : SS k r × (ℝ × ℝ) => conjM (aDil k r (ψ q)) (φ q)) (Set.univ ×ˢ Quad) := by
  have h1 : ContinuousOn (fun q : SS k r × (ℝ × ℝ) => aDil k r (ψ q)) (Set.univ ×ˢ Quad) :=
    (aDil_continuousOn k r).comp hψ.continuousOn hpos
  have h2 : ContinuousOn (fun q : SS k r × (ℝ × ℝ) => (aDil k r (ψ q))⁻¹) (Set.univ ×ˢ Quad) :=
    (aDil_inv_continuousOn k r).comp hψ.continuousOn hpos
  have h3 : ContinuousOn (fun q : SS k r × (ℝ × ℝ) => (Matrix.of (φ q) : Mat k r)) (Set.univ ×ˢ Quad) :=
    hφ.continuousOn
  exact (h1.mul h3).mul h2
end Formalism.FourierDecayAlt.P.B6
