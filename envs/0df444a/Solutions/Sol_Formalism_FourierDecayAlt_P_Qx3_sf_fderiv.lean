-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx3.sf_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:24:57.182876+00:00
-- url     : https://prove2.me/submissions/adbf5ed2-d2fd-4748-822d-3b843c4a8ddd

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_fam_hasFDerivAt
import Theorems.Thm_Formalism_REAL_withTop_enat_infty_add_one_le_infty


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {i : Fin (r + 1)} {U₀ : Set (XX k r)}
namespace Formalism.FourierDecayAlt.P.Qx3
theorem _root_.solution (v : Fin r → ℂ) {Φ : Fn k r E} (h : SmoothFam k r i U₀ Φ) :
    SmoothFam k r i U₀ (fun c g => fderiv ℝ (fun c' => Φ c' g) c v) := by
  intro x₀ hx₀ hg₀
  obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := h x₀ hx₀ hg₀
  refine ⟨U, fun x => fderiv ℝ F x ((v, 0) : XX k r), hU, hxU, ?_, ?_⟩
  · exact (hF.fderiv_of_isOpen (m := ∞) hU withTop_enat_infty_add_one_le_infty).clm_apply contDiffOn_const
  · intro x hx hxG
    show fderiv ℝ (fun c' => Φ c' x.2) x.1 v = _
    rw [(fam_hasFDerivAt hU hF hΦ hx hxG).fderiv]
    rfl
end Formalism.FourierDecayAlt.P.Qx3
