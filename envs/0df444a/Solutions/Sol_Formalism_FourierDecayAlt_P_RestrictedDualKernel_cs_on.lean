-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RestrictedDualKernel.cs_on
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:22:37.776281+00:00
-- url     : https://prove2.me/submissions/16c496cb-4ec5-4f3e-8bfe-e268d924cc67

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualKernelLemmas
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictedDualKernel
import Theorems.Thm_Formalism_FourierDecayAlt_P_GramProductIdentities_cs_of_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_GramProductIdentities_frmS_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RestrictedDualKernel
open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.DualKernelLemmas
open scoped Matrix ComplexOrder
variable {A S V : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
  [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]
namespace Formalism.FourierDecayAlt.P.RestrictedDualKernel
theorem _root_.solution (ρ : Rep A V) (M : SlopeTestRemainingChoices S A) (X : Submodule ℂ (Ix S → V)) (hP : IsPosOn ρ M X)
    {x y : Ix S → V} (hx : x ∈ X) (hy : y ∈ X) :
    ‖frm ρ M x y‖ ^ 2 ≤ (frm ρ M x x).re * (frm ρ M y y).re := by
  let Ξ : Formalism.FourierDecayAlt.F7.Sesq X :=
    LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun u v : X => frmS ρ M u v)
      (fun u v z => by simp) (fun c u z => by simp) (fun u v z => by simp) (fun c u z => by simp)
  have h := cs_of_pos Ξ (fun m => hP m.1 m.2) ⟨x, hx⟩ ⟨y, hy⟩
  simpa [Ξ, frmS_apply] using h
end Formalism.FourierDecayAlt.P.RestrictedDualKernel
