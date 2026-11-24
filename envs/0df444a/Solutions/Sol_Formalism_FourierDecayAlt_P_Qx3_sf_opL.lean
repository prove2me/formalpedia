-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx3.sf_opL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:55:25.796197+00:00
-- url     : https://prove2.me/submissions/7d817ab2-9c31-4eef-b02e-9d1c44fae7a3

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sf_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sf_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sf_csmul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sf_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_isOpen_OmXX
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sf_congr_on
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sf_ofC
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sf_fderiv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_cd_coord
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_cd_coordBar

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
theorem _root_.solution (hU₀ : U₀ ⊆ {x | x.1 ∈ OmX r}) (a : Fin r) (j : Fin 6) {Φ : Fn k r E}
    (h : SmoothFam k r i U₀ Φ) : SmoothFam k r i U₀ (crd (opL a j) Φ) := by
  have hw : SmoothFam k r i U₀ (fun c g => wirt a (fun c' => Φ c' g) c) :=
    sf_csmul _ (sf_sub (sf_fderiv _ h) (sf_csmul _ (sf_fderiv _ h)))
  have hwb : SmoothFam k r i U₀ (fun c g => wirtBar a (fun c' => Φ c' g) c) :=
    sf_csmul _ (sf_add (sf_fderiv _ h) (sf_csmul _ (sf_fderiv _ h)))
  have hc : SmoothFam k r i U₀ (fun c _ => c a) := sf_ofC (cd_coord a).contDiffOn hU₀
  have hcb : SmoothFam k r i U₀ (fun c _ => star (c a)) := sf_ofC (cd_coordBar a).contDiffOn hU₀
  have hci : SmoothFam k r i U₀ (fun c _ => (c a)⁻¹) :=
    sf_ofC ((cd_coord a).contDiffOn.inv fun x hx => hx a) hU₀
  have hcbi : SmoothFam k r i U₀ (fun c _ => (star (c a))⁻¹) :=
    sf_ofC ((cd_coordBar a).contDiffOn.inv fun x hx => star_ne_zero.2 (hx a)) hU₀
  fin_cases j
  · refine sf_congr_on isOpen_OmXX hU₀ (fun x hx _ => ?_) (sf_smul hc hw)
    show pOp a (fun c' => Φ c' x.2) x.1 = _
    unfold pOp
    exact if_pos hx
  · exact sf_smul hc h
  · exact sf_smul hci h
  · refine sf_congr_on isOpen_OmXX hU₀ (fun x hx _ => ?_) (sf_smul hcb hwb)
    show pbOp a (fun c' => Φ c' x.2) x.1 = _
    unfold pbOp
    exact if_pos hx
  · exact sf_smul hcb h
  · exact sf_smul hcbi h
end Formalism.FourierDecayAlt.P.Qx3
