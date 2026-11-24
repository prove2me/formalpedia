-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx3.fam_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:06:36.727688+00:00
-- url     : https://prove2.me/submissions/85050158-55bd-43ca-910b-7dea5b47cbff

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_glev_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_glev_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sf_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_isOpen_OmXX
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sf_ofC
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_cdo_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_ffl_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_ffl_smul

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
variable {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
variable {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
namespace Formalism.FourierDecayAlt.P.Qx3
theorem _root_.solution {j i : Fin (r + 1)} (hji : j ≤ i) {w : (Fin r → ℂ) → Mx k r} {ρ : (Fin r → ℂ) → ℂ}
    (hw : ContDiffOn ℝ ∞ w (OmX r)) (hρ : ContDiffOn ℝ ∞ ρ (OmX r))
    (hwG : ∀ c ∈ OmX r, w c ∈ Glev k r j) (hcomm : ∀ c ∈ OmX r, ∀ g ∈ Glev k r i, w c * g = g * w c)
    {D : Set (Mx k r)} {J : Mx k r → (Wq →L[ℂ] Wp)} (hJ : J ∈ FFl k r z z' π π' j D) :
    FamFF k r z z' π π' i (fun c => {g | w c * g ∈ D}) (fun c g => ρ c • J (w c * g)) := by
  refine ⟨?_, fun c hc => ffl_smul (ρ c) (ffl_res hji (hwG c hc) (hcomm c hc) hJ)⟩
  refine sf_smul (sf_ofC hρ (fun x hx => hx.1)) ?_
  rintro x₀ ⟨hc₀, hD₀⟩ hG₀
  obtain ⟨U, F, hU, hgU, hF, hJF⟩ :=
    hJ.1 (w x₀.1 * x₀.2) ⟨glev_mul (hwG _ hc₀) (glev_mono hji hG₀), hD₀⟩
  have hm : ContDiffOn ℝ ∞ (fun x : XX k r => w x.1 * x.2) {x | x.1 ∈ OmX r} :=
    cdo_mul (hw.comp contDiff_fst.contDiffOn (fun _ h => h)) contDiff_snd.contDiffOn
  exact ⟨{x | x.1 ∈ OmX r} ∩ (fun x : XX k r => w x.1 * x.2) ⁻¹' U, fun x => F (w x.1 * x.2),
    hm.continuousOn.isOpen_inter_preimage isOpen_OmXX hU, ⟨hc₀, hgU⟩,
    hF.comp (hm.mono Set.inter_subset_left) (fun x hx => hx.2),
    fun x hx hxG => hJF _ hx.2 (glev_mul (hwG _ hx.1) (glev_mono hji hxG))⟩
end Formalism.FourierDecayAlt.P.Qx3
