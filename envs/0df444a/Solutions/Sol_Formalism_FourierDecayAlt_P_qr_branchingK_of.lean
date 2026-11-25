-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.qr_branchingK_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:51:10.941832+00:00
-- url     : https://prove2.me/submissions/ddeab530-e8d1-41b5-9fa8-73e2c412ea7a

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameExtension
import Theorems.Thm_Formalism_FourierDecayAlt_P_FrameExtension_frame_weaken
import Theorems.Thm_Formalism_FourierDecayAlt_P_FrameExtension_frame_snoc
import Theorems.Thm_Formalism_FourierDecayAlt_P_FrameExtension_subA_EB
import Theorems.Thm_Formalism_FourierDecayAlt_P_FrameExtension_prod_Icc_fin
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr
import Theorems.Thm_Formalism_FourierDecayAlt_Qr_mem_CapSp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.QrD
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Qr.BranchingAlg → Qr.FrameGl → Qr.LieStab → Qr.StabLie → Qr.FrameChange →
    Qr.FrameExists2 → Qr.BranchingK := by
  intro hBA hFG hLS hSL hFC hFE Wp _ _ _ n r z e π u β L hz hT hty hL hu he hez hee
  obtain ⟨hnt, hrep, hcont, -, hirr, hcap⟩ := hty
  have hR : IsRepW (n + 1) r z π := ⟨hrep, hcont⟩
  obtain ⟨Bs₀, hB₀⟩ := hFE n r z e hz hT he hez hee
  have hB₁ := FrameExtension.frame_snoc hB₀ he hez hee
  set Bs₁ : Fin (n + 1) → Fin (2 * r + (n + 1) + 1) → ℂ :=
    Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ) Bs₀ e with hBs₁
  have hsub : subA (EB π Bs₁) = EB π Bs₀ := FrameExtension.subA_EB π Bs₀ e
  obtain ⟨hgl, hq⟩ := hFG Wp (n + 1) r (n + 1) z π Bs₁ hR hB₁
  have hH : Hyp (EB π Bs₁) β L := by
    refine ⟨hgl, ⟨hnt, fun S hS => hirr S (hLS Wp (n + 1) r z π Bs₁ hz hT hR hB₁ S hS)⟩, hL, ?_⟩
    intro w v
    rw [← hq w v, hcap Bs₁ hB₁ w v, FrameExtension.prod_Icc_fin]
    congr 1
    unfold cpol shf
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [← hu j]
    ring
  obtain ⟨hint, hS⟩ := hBA Wp n (EB π Bs₁) β L hH
  rw [hsub] at hint hS
  refine ⟨fun M => CapSp (EB π Bs₀) (shf β M.1), hint, fun M => ⟨(hS M).1, fun S' hle hst => ?_⟩, ?_⟩
  · exact (hS M).2 S' hle (hSL Wp (n + 1) r n z e π Bs₀ hR hB₀ S' hst)
  · intro Bs hBs M w v hv
    rw [(hFG Wp (n + 1) r n z π Bs hR (FrameExtension.frame_weaken hBs)).2 w v,
      hFC Wp n r z e π Bs Bs₀ hz hT he hez hee hR hBs hB₀ w]
    exact Qr.mem_CapSp.1 hv w
end Formalism.FourierDecayAlt.P
