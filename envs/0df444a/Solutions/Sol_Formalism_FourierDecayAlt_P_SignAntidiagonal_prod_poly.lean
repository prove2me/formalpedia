-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.prod_poly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:14:55.665812+00:00
-- url     : https://prove2.me/submissions/60f46d0e-b646-4b6a-be13-5c9bbc78c4f9

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RightDerivativeRulePsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PlMonoConst
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pl_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pl_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pl_lmul
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pl_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pl_mulu
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pl_mono_const
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
variable {A : Type} [Ring A] [Algebra ℂ A]
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution : ∀ (t : ℕ) (c δ : Fin t → ℂ) (F : Fin t → A),
    PolyLe t (fun u => (List.ofFn fun k => algebraMap ℂ A ((u + c k) * δ k) + F k).prod -
      algebraMap ℂ A (u ^ t * ∏ k, δ k)) := by
  intro t
  induction t with
  | zero =>
    intro c δ F
    exact ⟨Fin.elim0, fun u => by simp⟩
  | succ t ih =>
    intro c δ F
    obtain ⟨C, hC⟩ := ih (fun k => c k.succ) (fun k => δ k.succ) (fun k => F k.succ)
    let Q : ℂ → A := fun u => ∑ l : Fin t, algebraMap ℂ A (u ^ (l : ℕ)) * C l
    have hQpl : PolyLe t Q := ⟨C, fun u => rfl⟩
    have hR : ∀ u, (List.ofFn fun k : Fin t => algebraMap ℂ A ((u + c k.succ) * δ k.succ) + F k.succ).prod =
        algebraMap ℂ A (u ^ t * ∏ k : Fin t, δ k.succ) + Q u := by
      intro u
      show _ = _ + ∑ l : Fin t, algebraMap ℂ A (u ^ (l : ℕ)) * C l
      have h := hC u
      dsimp only at h
      rw [← h]
      abel
    refine pl_congr (f := fun u => algebraMap ℂ A (δ 0) * (Q u * algebraMap ℂ A u) +
        ((algebraMap ℂ A (c 0 * δ 0) + F 0) * Q u + algebraMap ℂ A (u ^ t) *
          ((algebraMap ℂ A (c 0 * δ 0) + F 0) * algebraMap ℂ A (∏ k : Fin t, δ k.succ)))) ?_
      (pl_add (pl_lmul _ (pl_mulu hQpl)) (pl_add (pl_mono (pl_lmul _ hQpl)) (pl_mono_const t _)))
    intro u
    simp only [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]
    rw [hR u]
    have e1 : algebraMap ℂ A (u * δ 0) * algebraMap ℂ A (u ^ t * ∏ k : Fin t, δ k.succ) =
        algebraMap ℂ A (u ^ (t + 1) * (δ 0 * ∏ k : Fin t, δ k.succ)) := by
      rw [← map_mul]
      congr 1
      ring
    have e2 : algebraMap ℂ A (u * δ 0) * Q u = algebraMap ℂ A (δ 0) * (Q u * algebraMap ℂ A u) := by
      rw [← Algebra.commutes, ← mul_assoc, ← map_mul, mul_comm (δ 0) u]
    have e3 : (algebraMap ℂ A (c 0 * δ 0) + F 0) * algebraMap ℂ A (u ^ t * ∏ k : Fin t, δ k.succ) =
        algebraMap ℂ A (u ^ t) * ((algebraMap ℂ A (c 0 * δ 0) + F 0) *
          algebraMap ℂ A (∏ k : Fin t, δ k.succ)) := by
      rw [map_mul (algebraMap ℂ A) (u ^ t), Algebra.left_comm]
    rw [add_mul u (c 0) (δ 0), map_add, add_assoc,
      mul_add (algebraMap ℂ A (u * δ 0) + (algebraMap ℂ A (c 0 * δ 0) + F 0)),
      add_mul (algebraMap ℂ A (u * δ 0)) _ (algebraMap ℂ A (u ^ t * ∏ k : Fin t, δ k.succ)),
      add_mul (algebraMap ℂ A (u * δ 0)) _ (Q u), e1, e2, e3]
    abel
end Formalism.FourierDecayAlt.P.SignAntidiagonal
