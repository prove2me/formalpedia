-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RealWeightedForms.regL_of_cnd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:22:39.39483+00:00
-- url     : https://prove2.me/submissions/0b515cf6-9eae-47f8-97d8-931d9c0fbe60

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualKernelLemmas
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RealWeightedForms

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
variable {S : Type}
namespace Formalism.FourierDecayAlt.P.RealWeightedForms
theorem _root_.solution {l l' : Letter ℂ S} (h : Cnd l l') : RegL l' l.pt := by
  unfold Cnd at h
  unfold RegL
  cases hp : l'.plus
  · simp only [hp, Bool.false_eq_true, if_false] at h ⊢
    intro he
    have hre := congrArg Complex.re he
    simp only [Complex.sub_re, Complex.one_re] at hre
    rw [hre] at h
    norm_num at h
  · simp only [hp, if_true] at h ⊢
    intro he
    have hre := congrArg Complex.re he
    simp only [Complex.sub_re, Complex.one_re] at hre
    rw [hre] at h
    norm_num at h
end Formalism.FourierDecayAlt.P.RealWeightedForms
