-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.map_measure_dilation_pair_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:07:17.107556+00:00
-- url     : https://prove2.me/submissions/0be5de8f-b035-4adb-8820-cface4ca355a

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_haar_sigmaFinite

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
theorem _root_.solution (hJ : DilJac D) {t : ℝ × ℝ} (h1 : 0 < t.1) (h2 : 0 < t.2) :
    D.μSS.map (dilation₂ t) =
      (ENNReal.ofReal ((t.1 ^ kap k r)⁻¹) * ENNReal.ofReal ((t.2 ^ kap k r)⁻¹)) • D.μSS := by
  have := haar_sigmaFinite D.haarW
  have := haar_sigmaFinite D.haarN
  have := haar_sigmaFinite D.haarW'
  have c1 := (BesselUnitaryEquiv.continuous_conjM (k := k) (r := r) (aDil k r t.1)).measurable
  have c2 := (BesselUnitaryEquiv.continuous_conjM (k := k) (r := r) (aDil k r t.2)).measurable
  have e : dilation₂ (k := k) (r := r) t =
      Prod.map (Prod.map id (conjM (aDil k r t.1))) (Prod.map id (conjM (aDil k r t.2))) := rfl
  unfold RealPlaceData.μSS
  rw [e, ← Measure.map_prod_map _ _ (measurable_id.prodMap c1) (measurable_id.prodMap c2),
    ← Measure.map_prod_map _ _ measurable_id c1, ← Measure.map_prod_map _ _ measurable_id c2,
    Measure.map_id, Measure.map_id, hJ t.1 h1, hJ t.2 h2, Measure.prod_smul_right, Measure.prod_smul_right,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
end Formalism.FourierDecayAlt.P.B6
