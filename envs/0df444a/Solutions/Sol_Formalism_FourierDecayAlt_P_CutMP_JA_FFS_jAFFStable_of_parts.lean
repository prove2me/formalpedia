-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.JA.FFS.jAFFStable_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:39:08.89422+00:00
-- url     : https://prove2.me/submissions/46f9907d-e0f1-4481-b1e8-c49fc98426da

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAFFStable2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAFFStableAsm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_GV_closed
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_ckOn_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA Formalism.FourierDecayAlt.P.CutMP.JA.FFS
open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS
theorem _root_.solution (hG : GermOps) (hE : ExtLoc) (hS : SmoothOps) (hA : AdjComm) (hQ : EquivOps)
    (hO : OmPDom) : JAFFStable := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ _ v Θ hΘ J hJ
  obtain ⟨hDom, hPos⟩ := hO E Wp Wq S T v
  have hG' := hG S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) Θ
  have hsupp : ∀ f' : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)), tsupport f' ⊆ OmP S T v →
      B.SuppIn (B.GPos (T v).base) f' := by
    intro f' hs x hx
    have hxG : x ∈ B.GV S.G.k S.G.r :=
      (Formalism.FourierDecayAlt.P.B5.GV_closed (k := S.G.k) (r := S.G.r)).closure_subset_iff.2 (fun y hy => hy.1) hx
    have hxT : x ∈ tsupport f' := closure_mono (fun y hy => hy.2) hx
    exact hPos x (hs hxT) hxG
  constructor
  · refine hQ hE _ _ _ _ (T v).base (OmP S T v) (B.opApply Θ) hDom
      (fun U f₁ f₂ hU he g hg hgG => (hG'.1 U f₁ f₂ hU he g hg hgG).1) (fun c f₁ g _ => (hG'.2 c f₁ g).1)
      (fun f₁ hf hs => (hS _ _ _ _ (T v).base Θ _ hDom.1 hPos hΘ.1 f₁ hf hs).1) ?_ J hJ
    intro f₁ hf _ _ p hp g hg hgG
    exact hΘ.2 p hp f₁ (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hf) g (hPos g hg hgG)
  · refine hQ hE _ _ _ _ (T v).base (OmP S T v) (B.opAdj Θ) hDom
      (fun U f₁ f₂ hU he g hg hgG => (hG'.1 U f₁ f₂ hU he g hg hgG).2) (fun c f₁ g _ => (hG'.2 c f₁ g).2)
      (fun f₁ hf hs => (hS _ _ _ _ (T v).base Θ _ hDom.1 hPos hΘ.1 f₁ hf hs).2) ?_ J hJ
    intro f₁ hf hc hs p hp g hg hgG
    exact hA _ _ _ _ (T v).base Θ hΘ.1 hΘ.2 f₁ hf hc (hsupp f₁ hs) p hp g (hPos g hg hgG)
end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
