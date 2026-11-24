-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.key_formal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:57:47.012856+00:00
-- url     : https://prove2.me/submissions/5758bcf9-b4fa-4b6d-b77b-1db605517891

import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DetRowsZero
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_two_formal
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_four_formal

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL
variable {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}
namespace Formalism.FourierDecayAlt.P.JFxE
theorem _root_.solution (E : Fin n → Fin n → A) {m : ℕ} (a b : Fin (m + 1) → Fin n) (i : Fin m) (u : ℂ)
    (σ : Equiv.Perm (Fin (m + 1))) :
    exchangeTwo_self_eq_one E a b u σ - exchangeTwo_self_eq_one E a b u (σ * Equiv.swap i.castSucc i.succ)
      + exchangeTwo_self_eq_one E a (b ∘ Equiv.swap i.castSucc i.succ) u σ
      - exchangeTwo_self_eq_one E a (b ∘ Equiv.swap i.castSucc i.succ) u (σ * Equiv.swap i.castSucc i.succ) =
      Lt E a b u σ i * Md E a b σ i * Rt E a b u σ i := by
  have hs : ∀ k : Fin (m + 1), (k : ℕ) ≠ (i : ℕ) → (k : ℕ) ≠ (i : ℕ) + 1 →
      Equiv.swap i.castSucc i.succ k = k := by
    intro k h1 h2
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h; apply h1; rw [h]; simp
    · intro h; apply h2; rw [h]; simp
  unfold exchangeTwo_self_eq_one Lt Rt
  rw [four_formal _ _ _ _ (i : ℕ) (by omega)]
  · congr 2
    have e1 : (⟨(i : ℕ), by omega⟩ : Fin (m + 1)) = i.castSucc := rfl
    have e2 : (⟨(i : ℕ) + 1, by omega⟩ : Fin (m + 1)) = i.succ := rfl
    simp only [e1, e2, Equiv.Perm.mul_apply, Function.comp_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_right, Md]
    exact two_formal E _ _ (by simp) _ _ _ _
  · intro k h1 h2; simp [Equiv.Perm.mul_apply, hs k h1 h2]
  · intro k h1 h2; simp [hs k h1 h2]
  · intro k h1 h2; simp [Equiv.Perm.mul_apply, hs k h1 h2]
end Formalism.FourierDecayAlt.P.JFxE
