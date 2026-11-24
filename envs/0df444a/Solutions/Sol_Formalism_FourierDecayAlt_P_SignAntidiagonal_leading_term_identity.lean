-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.leading_term_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:09:34.119176+00:00
-- url     : https://prove2.me/submissions/23eebd3b-26a8-49ef-8a19-e14b834967aa

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PlMonoConst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeadingTermIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_perm_id_of_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_top_self
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_prod_ne_zero_imp
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pe_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pl_lmul
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pl_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pl_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_ps_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_qminor_poly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.pe_val
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.ps_val


section
open Matrix Finset
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants
private theorem leading_term_identity_lemma {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A)
    (P : (Fin m → Fin n) → Prop) [DecidablePred P] (d : (Fin m → Fin n) → ℂ)
    (fa fb : (Fin m → Fin n) → Fin m → Fin n) (s0 : ℂ) (c0 : Fin m → Fin n) (h0 : P c0)
    (h1 : ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, (if fa c0 (σ k) = fb c0 k then (1 : ℂ) else 0) = 1)
    (hz : ∀ c, P c → c ≠ c0 → ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, (if fa c (σ k) = fb c k then (1 : ℂ) else 0) = 0) :
    ∃ C : Fin m → A, ∀ u : ℂ, (∑ c, if P c then d c • qminor E (fa c) (fb c) (u + s0) else 0) =
      algebraMap ℂ A (u ^ m * d c0) + ∑ l : Fin m, algebraMap ℂ A (u ^ (l : ℕ)) * C l := by
  have hP : PolyLe m (fun u => ∑ c, if P c then algebraMap ℂ A (d c) *
      (qminor E (fa c) (fb c) (u + s0) - algebraMap ℂ A (u ^ m * ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, (if fa c (σ k) = fb c k then (1 : ℂ) else 0))) else 0) := by
    refine pl_sum Finset.univ (fun c u => if P c then algebraMap ℂ A (d c) *
      (qminor E (fa c) (fb c) (u + s0) - algebraMap ℂ A (u ^ m * ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, (if fa c (σ k) = fb c k then (1 : ℂ) else 0))) else 0)
      fun c _ => ?_
    by_cases hc : P c
    · simp only [hc, if_true]
      exact pl_lmul _ (qminor_poly E (fa c) (fb c) s0)
    · simp only [hc, if_false]
      exact pl_zero m
  obtain ⟨C, hC⟩ := hP
  refine ⟨C, fun u => ?_⟩
  rw [← hC u]
  beta_reduce
  have hsplit : ∀ c, (if P c then algebraMap ℂ A (d c) *
      (qminor E (fa c) (fb c) (u + s0) - algebraMap ℂ A (u ^ m * ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, (if fa c (σ k) = fb c k then (1 : ℂ) else 0))) else 0) =
      (if P c then d c • qminor E (fa c) (fb c) (u + s0) else 0) -
        (if P c then algebraMap ℂ A (u ^ m * (d c * ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, (if fa c (σ k) = fb c k then (1 : ℂ) else 0))) else 0) := by
    intro c
    split_ifs
    · rw [mul_sub, Algebra.smul_def, ← map_mul]
      congr 2
      ring
    · simp
  have hsecond : (∑ c, if P c then algebraMap ℂ A (u ^ m * (d c * ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, (if fa c (σ k) = fb c k then (1 : ℂ) else 0))) else 0) =
      algebraMap ℂ A (u ^ m * d c0) := by
    rw [Finset.sum_eq_single c0]
    · rw [if_pos h0, h1, mul_one]
    · intro c _ hc
      split_ifs with hPc
      · rw [hz c hPc hc, mul_zero, mul_zero, map_zero]
      · rfl
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [Finset.sum_congr rfl fun c _ => hsplit c, Finset.sum_sub_distrib, hsecond]
  abel
end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution : LeadAA := by
  intro A _ _ k r E xi m hm
  classical
  have hxv : ∀ l, (xR k r m hm l).val = l.val := fun l => rfl
  have hxinj : Function.Injective (xR k r m hm) := fun a b h => Fin.ext (by rw [← hxv a, ← hxv b, h])
  have hxm : StrictMono (xR k r m hm) := fun a b hab => Fin.lt_def.mpr (by rw [hxv, hxv]; exact hab)
  obtain ⟨C, hC⟩ := leading_term_identity_lemma E (fun c => StrictMono c)
    (fun c => (Matrix.of fun a l : Fin m => xi (Fin.castLE hm a) (c l)).det)
    (fun _ => xR k r m hm) id 0 (xR k r m hm) hxm (top_self _ hxinj) (by
      intro c hc hne
      by_contra hs
      obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
      have heq := prod_ne_zero_imp (xR k r m hm) c σ (right_ne_zero_of_mul hσ)
      have hσm : StrictMono (fun l => (σ l).val) := by
        intro a b hab
        have h1 : c a < c b := hc hab
        rw [← heq a, ← heq b, Fin.lt_def, hxv, hxv] at h1
        exact h1
      have hσ1 := perm_id_of_mono σ hσm
      apply hne
      funext l
      rw [← heq l, hσ1]
      rfl)
  refine ⟨C, fun u => ?_⟩
  have h := hC u
  simp only [id, add_zero] at h
  unfold AAx
  exact h
end Formalism.FourierDecayAlt.P.SignAntidiagonal
