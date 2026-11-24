-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.AAx_head
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:33:51.144781+00:00
-- url     : https://prove2.me/submissions/0aff9fea-7ac7-4de0-b2b5-9d2cf3e7972f

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThirdPeelingMinorMemIdeal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AAvCongr
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_sum_single
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_uniq_mono
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution {A : Type} [Ring A] [Algebra ℂ A] (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A)
    (xi : Fin r → Fin (2 * r + k + 1) → ℂ) (i0 : ℕ) (hi0 : i0 ≤ r) (h : Matrix (Fin i0) (Fin i0) ℂ) (u : ℂ)
    (hz : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < i0 → i0 ≤ p.val → xi a p = 0)
    (hh : ∀ a b : Fin i0, xi (Fin.castLE hi0 a) (xR k r i0 hi0 b) = h a b) :
    AAx k r E xi i0 hi0 u = h.det • qminor E (xR k r i0 hi0) (xR k r i0 hi0) u := by
  unfold AAx
  rw [sum_single (fun c => StrictMono c) (fun a p => xi (Fin.castLE hi0 a) p) (Set.range (xR k r i0 hi0))
    ?_ (xR k r i0 hi0) ?_ ?_]
  · congr 2
    ext a l
    simp only [Matrix.of_apply]
    exact hh a l
  · intro a p hp
    apply hz _ _ (by simp)
    by_contra hlt; push Not at hlt; apply hp; exact ⟨⟨p.val, hlt⟩, by ext; simp [xR, eI]⟩
  · intro a b hab; simp only [xR, eI]; exact hab
  · intro c hc hS
    exact uniq_mono _ _ (fun a b hab => by simp only [xR, eI]; exact hab) hc hS
end Formalism.FourierDecayAlt.P.SignAntidiagonal
