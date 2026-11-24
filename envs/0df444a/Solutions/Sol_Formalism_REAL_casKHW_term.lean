-- Prove2me | solution 1 for Formalism.REAL.casKHW_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:34:06.124728+00:00
-- url     : https://prove2.me/submissions/483dcb5a-1459-41e3-8ae2-b52bdddfcc19

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementA
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CasKHW

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (μ : Fin n → ℝ) (w : V)
    (hG : GlRel E) (hK : KHighest ε E μ w) (a b : Fin n) :
    (if ε a = ε b then E a b * E b a else 0) w = ((casKHW_coef ε μ a b : ℝ) : ℂ) • w := by
  unfold casKHW_coef
  by_cases h : ε a = ε b
  · simp only [h, if_true]
    rcases lt_trichotomy a b with hab | rfl | hab
    · have hne : a ≠ b := ne_of_lt hab
      simp only [hne, if_false, hab, if_true]
      have h1 := congrArg (fun T : Module.End ℂ V => T w) (hG a b b a)
      simp only [if_true, LinearMap.sub_apply, Module.End.mul_apply] at h1
      have h0 : E a b w = 0 := hK.2 a b hab h
      rw [h0, map_zero, sub_zero, hK.1 a, hK.1 b] at h1
      rw [Module.End.mul_apply, h1]
      push_cast
      rw [sub_smul]
    · simp only [if_true, Module.End.mul_apply, hK.1 a, map_smul, smul_smul]
      push_cast; ring_nf
    · have hne : a ≠ b := ne_of_gt hab
      have hnl : ¬ a < b := not_lt_of_gt hab
      simp only [hne, if_false, hnl]
      rw [Module.End.mul_apply, hK.2 b a hab h.symm, map_zero]
      simp
  · simp [h]
end Formalism.REAL
