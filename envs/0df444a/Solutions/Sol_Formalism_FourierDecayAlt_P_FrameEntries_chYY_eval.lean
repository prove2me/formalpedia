-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FrameEntries.chYY_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:08:07.677498+00:00
-- url     : https://prove2.me/submissions/77e6afc0-5509-4752-8b5f-56fe77a0e63e

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameEntries
import Theorems.Thm_Formalism_FourierDecayAlt_P_FrameEntries_chatA_eval
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_rep_etaV
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_rep_yV


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.FrameEntries
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.FrameEntries
theorem _root_.solution (hD : IsOpen D) (z : Fin (2 * r + k + 1) → ℂ) (u : ℂ) (ψ : SV k r i D E) {g : Mx k r}
    (hg : g ∈ Glev k r i ∩ D) :
    (chYY (EV k r i D E) u (yV k r z i D E) (etaV k r z i D E) ψ).1 g =
      (chatA (EV k r i D E) u (yv k r z i g) (ybv k r z i g) ψ).1 g := by
  rw [chatA_eval]
  unfold chYY
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
    Pi.smul_apply]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  have h1 : ((etaV k r z i D E p * yV k r z i D E q * qminor (EV k r i D E) (skip1 p) (skip1 q) u) ψ).1 g =
      ybv k r z i g p • yv k r z i g q • (qminor (EV k r i D E) (skip1 p) (skip1 q) u ψ).1 g := by
    show (etaV k r z i D E p (yV k r z i D E q (qminor (EV k r i D E) (skip1 p) (skip1 q) u ψ))).1 g = _
    rw [(OperatorRepresentations.rep_etaV hD z p).2 _ g hg]
    show ybv k r z i g p • (yV k r z i D E q (qminor (EV k r i D E) (skip1 p) (skip1 q) u ψ)).1 g = _
    rw [(OperatorRepresentations.rep_yV hD z q).2 _ g hg]
    rfl
  rw [h1, smul_smul, smul_smul]
end Formalism.FourierDecayAlt.P.FrameEntries
