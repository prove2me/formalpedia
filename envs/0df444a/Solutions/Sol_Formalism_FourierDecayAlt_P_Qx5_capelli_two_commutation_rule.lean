-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx5.capelli_two_commutation_rule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:50:46.847709+00:00
-- url     : https://prove2.me/submissions/8a2c7acd-23a7-41ea-930f-42016fc3f1df

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_ch_rule
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_ch_dc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


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
theorem _root_.solution (h : ComRule k r i D E c g ρ κ s d) (hs : s ≠ 0) (hc : SmoothLev k r i D c)
    (A B : Fin (mdim k r i) → ℂ) (w : ℂ) {f : Mx k r → E} (hf : SmoothLev k r i D f) :
    ch2 k r i A ρ B κ (w - d) (fun y => c y • f y) g = c g • ch2 k r i A ρ B κ (w - d) f g := by
  have e1 := ch_rule h A B w (smooth_mul hc hf)
  have e2 := ch_rule h A B w hf
  rw [ch_dc h hc A B w hf] at e1
  have e3 : s • ch2 k r i A ρ B κ (w - d) (fun y => c y • f y) g = s • (c g • ch2 k r i A ρ B κ (w - d) f g) := by
    have e4 : s • ch2 k r i A ρ B κ (w - d) f g = ch k r i A B w (fun y => c y • f y) g - c g • ch k r i A B w f g := by
      rw [e2]; abel
    have e5 : s • ch2 k r i A ρ B κ (w - d) (fun y => c y • f y) g =
        (2 * c g) • ch k r i A B w (fun y => c y • f y) g - (c g ^ 2) • ch k r i A B w f g -
          c g • ch k r i A B w (fun y => c y • f y) g := by
      rw [e1]; abel
    rw [e5, smul_comm s, e4]
    module
  exact smul_right_injective E hs e3
end Formalism.FourierDecayAlt.P.Qx5
