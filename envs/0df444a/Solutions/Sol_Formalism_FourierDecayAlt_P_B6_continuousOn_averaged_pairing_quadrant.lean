-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.continuousOn_averaged_pairing_quadrant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:02:47.066389+00:00
-- url     : https://prove2.me/submissions/6b9fd2e0-ca3c-46ab-890d-34a048aed4a3

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_QR_continuousOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissibleWeight_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_cutoff_gamma_product_continuous

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
theorem _root_.solution (H : Hyp D Ξ α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ}
    (hF : AdmW α c 2 2 F) (hF' : AdmW α c' 2 2 F') :
    ContinuousOn (fun q : SS k r × (ℝ × ℝ) => Ef D F F' q.1 q.2) ({p | D.inSS p} ×ˢ Quad) := by
  unfold Ef
  refine continuousOn_finsetSum _ fun m hm => continuousOn_finsetSum _ fun l hl => ?_
  have hm' : m ≤ 2 := by have := Finset.mem_range.1 hm; omega
  have hl' : l ≤ 2 := by have := Finset.mem_range.1 hl; omega
  exact ((cutoff_gamma_product_continuous D m l).comp continuous_snd).continuousOn.mul
    (QR_continuousOn H (admissibleWeight_mono hF hl' hm') (admissibleWeight_mono hF' hl' hm'))
end Formalism.FourierDecayAlt.P.B6
