-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBG.Emir_gl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:28:58.072801+00:00
-- url     : https://prove2.me/submissions/5e2e23cd-4c8e-4c49-9a78-6b727e275a93

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGHead
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGHeadV
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_ep_sq
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_rv_rv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pe_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_ps_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.pe_val
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.ps_val



set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBG
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.SignAntidiagonal
variable {A : Type} [Ring A] [Algebra ℂ A] {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.PBG
theorem _root_.solution {E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A} (hE : Formalism.REAL.GlRel E) :
    Formalism.REAL.GlRel (Emir E) := by
  intro a b c d
  have hinj : ∀ x y : Fin (2 * r + k + 1), rv x = rv y ↔ x = y := fun x y =>
    ⟨fun h => by rw [← rv_rv x, h, rv_rv], fun h => h ▸ rfl⟩
  have key := hE (rv b) (rv a) (rv d) (rv c)
  simp only [hinj] at key
  have h1 : Emir E a b * Emir E c d - Emir E c d * Emir E a b =
      (ep a * ep b * (ep c * ep d)) •
        (E (rv b) (rv a) * E (rv d) (rv c) - E (rv d) (rv c) * E (rv b) (rv a)) := by
    simp only [Emir, neg_mul_neg, smul_mul_smul_comm, smul_sub, mul_comm (ep c * ep d) (ep a * ep b)]
  rw [h1, key]
  by_cases hbc : b = c
  · subst c
    by_cases hda : d = a
    · subst a
      have hs : ep d * ep b * (ep b * ep d) = 1 := by
        calc _ = (ep d * ep d) * (ep b * ep b) := by ring
          _ = 1 := by rw [ep_sq, ep_sq, mul_one]
      simp only [if_true, hs, one_smul, Emir, ep_sq, neg_sub_neg]
    · have hs : ep a * ep b * (ep b * ep d) = ep a * ep d := by
        calc _ = ep a * ep d * (ep b * ep b) := by ring
          _ = _ := by rw [ep_sq, mul_one]
      have had : ¬ a = d := fun e => hda e.symm
      simp only [if_true, had, hda, if_false, hs, Emir, zero_sub, sub_zero, smul_neg]
  · by_cases hda : d = a
    · subst a
      have hs : ep d * ep b * (ep c * ep d) = ep c * ep b := by
        calc _ = ep c * ep b * (ep d * ep d) := by ring
          _ = _ := by rw [ep_sq, mul_one]
      have hcb : ¬ c = b := fun e => hbc e.symm
      simp only [if_true, hcb, hbc, if_false, hs, Emir, zero_sub, sub_zero, neg_neg]
    · have had : ¬ a = d := fun e => hda e.symm
      have hcb : ¬ c = b := fun e => hbc e.symm
      simp only [had, hcb, hbc, hda, if_false, sub_zero, smul_zero]
end Formalism.FourierDecayAlt.P.PBG
