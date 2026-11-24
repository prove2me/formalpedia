-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW.fam_of_hw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:41:26.697704+00:00
-- url     : https://prove2.me/submissions/d5bb9ebc-6d1a-4140-9cc2-17ef6d40dfab

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAPRTWNeAlgSt
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IrreducibleCapelliModules
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreKLExistsOfAlg
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAPRTWNeAlg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_map_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA Formalism.FourierDecayAlt.P.CutMP.JA.SSn Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW
theorem _root_.solution {n : ℕ} {F : Fin n → Fin n → Module.End ℂ V} {Z : Fin n → Module.End ℂ V} (hZ : IsVec F Z)
    (ν : Fin n → ℂ) (v : V) (hv : IsHW F ν v) :
    (∀ a c, F a a (Z c v) = (ν a - if a = c then 1 else 0) • Z c v) ∧
      ∀ a b c, a < b → F a b (Z c v) = if a = c then -(Z b v) else 0 := by
  obtain ⟨hdiag, hup⟩ := hv
  constructor
  · intro a c
    have h := congrArg (fun T : Module.End ℂ V => T v) (hZ a a c)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hdiag a, map_smul] at h
    by_cases hac : a = c
    · subst hac
      simp only [if_true, LinearMap.neg_apply] at h
      rw [if_pos rfl, sub_eq_iff_eq_add.mp h, sub_smul, one_smul]
      abel
    · simp only [if_neg hac, LinearMap.zero_apply] at h
      rw [if_neg hac, sub_zero]
      exact sub_eq_zero.mp h
  · intro a b c hab
    have h := congrArg (fun T : Module.End ℂ V => T v) (hZ a b c)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hup a b hab, map_zero, sub_zero] at h
    rw [h]
    split_ifs <;> simp
end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW
