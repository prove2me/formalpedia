-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx5.rd_addX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:28:51.278637+00:00
-- url     : https://prove2.me/submissions/559b06c6-3b12-47e3-8b78-24403c877c36

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_lie_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_rd_ext

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
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.Qx5
theorem _root_.solution {f : Mx k r → E} (hf : SmoothLev k r i D f) {g X Y : Mx k r} (hg : g ∈ Glev k r i ∩ D)
    (hX : inLieLev k r i X) (hY : inLieLev k r i Y) : RdV (X + Y) f g = RdV X f g + RdV Y f g := by
  obtain ⟨U, F, hU, hgU, hF, he⟩ := hf g hg
  rw [rd_ext hU hgU hg.1 (lie_add hX hY) hF he, rd_ext hU hgU hg.1 hX hF he, rd_ext hU hgU hg.1 hY hF he,
    Matrix.mul_add, map_add]
end Formalism.FourierDecayAlt.P.Qx5
