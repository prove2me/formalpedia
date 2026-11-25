-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx5.ev_QM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:57:43.322367+00:00
-- url     : https://prove2.me/submissions/53446f31-719e-4305-a4d1-98033571cb03

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_ev_M
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_rep_qminor
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_good_qminor


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
variable (z z' : Fin (2 * r + k + 1) → ℂ)
namespace Formalism.FourierDecayAlt.P.Qx5
theorem _root_.solution (hD : IsOpen D) {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (w : ℂ) {c : Mx k r → ℂ}
    (hc : SmoothLev k r i D c) {f : Mx k r → E} (hf : SmoothLev k r i D f) {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) :
    (qminor (Eh (E := E) hD) a b w (Mh hD c hc ⟨cut k r i D f, cut_mem hD hf⟩) : Mx k r → E) g =
      Mop k r i a b w (fun y => c y • f y) g := by
  rw [rep_qminor hD a b w _ g hg]
  refine (good_qminor hD a b w).loc _ _ (fun x hx => ?_) g hg
  rw [ev_M hD hc _ hx]
  show c x • cut k r i D f x = c x • f x
  rw [cut_of_mem f hx]
end Formalism.FourierDecayAlt.P.Qx5
