-- Prove2me | solution 1 for Formalism.QuantumDeterminants.formal_degree_perm_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:12:11.289349+00:00
-- url     : https://prove2.me/submissions/5345da9e-7312-450c-9344-0746dcea6d1f

import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSFdeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset
noncomputable section
namespace Formalism.QuantumDeterminants
open Formalism.REAL
private lemma fdNum_nonneg {n : ℕ} (lam : Fin n → ℝ) : 0 ≤ fdNum lam :=
  Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => abs_nonneg _
private lemma fdNum_sq {n : ℕ} (lam : Fin n → ℝ) : fdNum lam ^ 2 = fdFull lam := by
  unfold fdNum fdFull
  have key : ∀ a b : Fin n, (if a = b then (1 : ℝ) else |lam a - lam b|) =
      (if a < b then |lam a - lam b| else 1) * (if b < a then |lam b - lam a| else 1) := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.mpr h.le, abs_sub_comm]
  simp_rw [key, Finset.prod_mul_distrib, ← Finset.prod_filter]
  rw [sq]
  congr 1
  symm
  exact Finset.prod_comm' (by intro a b; simp)
private lemma fdFull_perm {n : ℕ} (lam : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    fdFull (lam ∘ σ) = fdFull lam := by
  unfold fdFull
  exact Fintype.prod_equiv σ _ _ fun a => Fintype.prod_equiv σ _ _ fun b => by
    simp [Equiv.apply_eq_iff_eq]
private lemma fdNum_perm {n : ℕ} (lam : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    fdNum (lam ∘ σ) = fdNum lam := by
  refine (pow_left_inj₀ (fdNum_nonneg _) (fdNum_nonneg _) two_ne_zero).mp ?_
  rw [fdNum_sq, fdNum_sq, fdFull_perm]
end Formalism.QuantumDeterminants
end
end

set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.REAL
namespace Formalism.QuantumDeterminants
theorem _root_.solution : FdegPerm := by
  intro n lam σ
  have h := fdNum_perm lam σ
  unfold fdNum at h
  unfold fdegHC
  rw [h]
end Formalism.QuantumDeterminants
