-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx5.ch_rule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:50:55.5028+00:00
-- url     : https://prove2.me/submissions/5ad24417-d9d1-43c0-bab5-20d190b92266

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_pairSum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr


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
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
variable {c : Mx k r → ℂ} {g : Mx k r} {ρ κ : Fin (mdim k r i) → ℂ} {s d : ℂ}
namespace Formalism.FourierDecayAlt.P.Qx5
theorem _root_.solution (h : ComRule k r i D E c g ρ κ s d) (A B : Fin (mdim k r i) → ℂ) (w : ℂ) {f : Mx k r → E}
    (hf : SmoothLev k r i D f) :
    ch k r i A B w (fun y => c y • f y) g = c g • ch k r i A B w f g + s • ch2 k r i A ρ B κ (w - d) f g := by
  have hp := pairSum (mdim k r i) A ρ B κ (fun l l' => Mop k r i l l' (w - d) f g)
  unfold ch ch2
  rw [← hp]
  simp only [h _ _ _ _ f hf, smul_add, Finset.sum_add_distrib, Finset.smul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [smul_comm]
  · refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p' _ =>
      Finset.sum_congr rfl fun q' _ => ?_
    simp only [smul_smul]
    congr 1
    ring
end Formalism.FourierDecayAlt.P.Qx5
