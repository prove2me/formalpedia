-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.adj_formal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:13:29.385966+00:00
-- url     : https://prove2.me/submissions/c328470a-cda8-4b40-9d8e-b31456a67ca4

import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DetRowsZero
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_key_formal
import Theorems.Thm_Formalism_REAL_quantumMinor_eq_sum_term


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
theorem _root_.solution (E : Fin n → Fin n → A) {m : ℕ} (a b : Fin (m + 1) → Fin n) (i : Fin m) (u : ℂ) :
    (2 : ℂ) • (qminor E a (b ∘ Equiv.swap i.castSucc i.succ) u + qminor E a b u) =
      ∑ σ : Equiv.Perm (Fin (m + 1)),
        ((Equiv.Perm.sign σ : ℤ) : A) * (Lt E a b u σ i * Md E a b σ i * Rt E a b u σ i) := by
  set s := Equiv.swap i.castSucc i.succ with hs_def
  have hsgn : Equiv.Perm.sign s = -1 := Equiv.Perm.sign_swap (by simp [Fin.ext_iff])
  set G : Equiv.Perm (Fin (m + 1)) → A := fun σ =>
    ((Equiv.Perm.sign σ : ℤ) : A) * (exchangeTwo_self_eq_one E a (b ∘ s) u σ + exchangeTwo_self_eq_one E a b u σ) with hG
  have hsum : qminor E a (b ∘ s) u + qminor E a b u = ∑ σ, G σ := by
    rw [quantumMinor_eq_sum_term, quantumMinor_eq_sum_term, ← Finset.sum_add_distrib]
    simp only [hG, mul_add]
  have hre : ∑ σ, G (σ * s) = ∑ σ, G σ := Fintype.sum_equiv (Equiv.mulRight s) _ _ (fun σ => rfl)
  have hpair : ∀ σ, G σ + G (σ * s) =
      ((Equiv.Perm.sign σ : ℤ) : A) * (Lt E a b u σ i * Md E a b σ i * Rt E a b u σ i) := by
    intro σ
    simp only [hG, Equiv.Perm.sign_mul, hsgn, mul_neg, mul_one, Units.val_neg, Int.cast_neg]
    have k := key_formal E a b i u σ
    rw [← hs_def] at k
    rw [← k]
    noncomm_ring
  rw [hsum, two_smul, ← Finset.sum_congr rfl (fun σ _ => hpair σ), Finset.sum_add_distrib, hre]
end Formalism.FourierDecayAlt.P.JFxE
