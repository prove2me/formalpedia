-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.strictMono_snoc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:17:34.172347+00:00
-- url     : https://prove2.me/submissions/437bf30a-dd60-445c-a31b-58d288d89a7c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondExpansionIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StrictMonoSnoc
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
theorem _root_.solution {α : Type} [Preorder α] {m : ℕ} (f : Fin m → α) (hf : StrictMono f) (x : α)
    (hx : ∀ l, f l < x) : StrictMono (Fin.snoc (α := fun _ => α) f x : Fin (m + 1) → α) := by
  intro a b hab
  induction b using Fin.lastCases with
  | last =>
    induction a using Fin.lastCases with
    | last => exact absurd hab (lt_irrefl _)
    | cast a =>
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      exact hx a
  | cast b =>
    induction a using Fin.lastCases with
    | last => exact absurd hab (not_lt.2 (Fin.castSucc_lt_last b).le)
    | cast a =>
      simp only [Fin.snoc_castSucc]
      exact hf (Fin.castSucc_lt_castSucc_iff.1 hab)
end Formalism.FourierDecayAlt.P.SignAntidiagonal
