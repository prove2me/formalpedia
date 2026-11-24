-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RealWeightedForms.frm_act_act_of_star_mul_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:22:34.908643+00:00
-- url     : https://prove2.me/submissions/4559d008-ec46-47f2-a100-6234c523be81

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualKernelLemmas
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RealWeightedForms
import Theorems.Thm_Formalism_FourierDecayAlt_P_GramProductIdentities_pairAdj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RealWeightedForms
open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.DualKernelLemmas
open scoped Matrix
variable {A S V : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
  [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]
namespace Formalism.FourierDecayAlt.P.RealWeightedForms
theorem _root_.solution (ρ : Rep A V) (RR W : SlopeTestRemainingChoices S A) (hW : star W * RR * W = RR) (X X' : Ix S → V) :
    frm ρ RR (act W X) (act W X') = frm ρ RR X X' := by
  have hPA := fun (M N : SlopeTestRemainingChoices S A) (Y Y' : Ix S → V) => GramProductIdentities.pairAdj A S V ρ M N 1 Y Y'
  unfold frm
  have h1 := (hPA (star W) 1 (act RR (act W X)) X').2.2.2
  rw [star_star] at h1
  rw [← h1, ← (hPA (star W) RR (act W X) X').1, ← (hPA (star W * RR) W X X').1, hW]
end Formalism.FourierDecayAlt.P.RealWeightedForms
