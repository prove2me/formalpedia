-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.quadrant_function_continuous_on
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:28:25.471239+00:00
-- url     : https://prove2.me/submissions/8747cb50-aef1-4ab5-ab22-02f156e9f160

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_dil_inSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_dilationAction_continuousOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissibleWeight_left_derivative
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissibleWeight_of_succ_left_order
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissible_of_weighted
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_ph_continuousOn

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
theorem _root_.solution (H : Hyp D Ξ α) {m : ℕ} {A B : Mat k r → (Wq →L[ℂ] Wp)} {cA cB : ℝ}
    (hA : AdmW α cA 0 m A) (hB : AdmW α cB 0 m B) :
    ContinuousOn (fun q : SS k r × (ℝ × ℝ) => QL D q.1 m A B q.2.1 q.2.2) ({p | D.inSS p} ×ˢ Quad) := by
  induction m generalizing A B with
  | zero =>
    have h1 := ph_continuousOn H (admissible_of_weighted hA) (admissible_of_weighted hB)
    have h2 : ContinuousOn (fun q : SS k r × (ℝ × ℝ) => dilation₂ q.2 q.1) ({p | D.inSS p} ×ˢ Quad) :=
      (dilationAction_continuousOn k r).mono (Set.prod_mono (Set.subset_univ _) le_rfl)
    refine h1.comp h2 ?_
    rintro ⟨p, t⟩ ⟨hp, ht⟩
    exact dil_inSS H.dilN D hp ht.1 ht.2
  | succ m ih => exact (ih (admissibleWeight_left_derivative hA) (admissibleWeight_of_succ_left_order hB)).add (ih (admissibleWeight_of_succ_left_order hA) (admissibleWeight_left_derivative hB))
end Formalism.FourierDecayAlt.P.B6
