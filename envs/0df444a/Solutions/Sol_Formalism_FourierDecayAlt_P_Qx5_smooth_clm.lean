-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx5.smooth_clm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:47:07.856793+00:00
-- url     : https://prove2.me/submissions/324d51a6-89f1-4b19-be63-1ff24b29f584

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MeasureTheory
open scoped ContDiff InnerProductSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Qx2
variable {k r : ℕ} {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  {i : Fin (r + 1)} {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.Qx5
theorem _root_.solution (φ : E →L[ℂ] E') {f : Mx k r → E} (hf : SmoothLev k r i D f) :
    SmoothLev k r i D (fun x => φ (f x)) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, he⟩ := hf g₀ hg₀
  refine ⟨U, fun x => φ (F x), hU, hgU, (φ.restrictScalars ℝ).contDiff.comp_contDiffOn hF, fun x hx hxG => ?_⟩
  show φ (f x) = φ (F x)
  rw [he x hx hxG]
end Formalism.FourierDecayAlt.P.Qx5
