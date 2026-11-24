-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.case3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:14:17.195842+00:00
-- url     : https://prove2.me/submissions/6ff99c37-5154-4e83-9afd-161e048c870c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_HasDerivAtPhase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_LeftMultiplicationRule
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_single_conj
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_fvec_es
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_ell_form
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_ell_dag_form
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_ginv_eq
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_e_out
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_es_out
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_core
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_glev_inv
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_glev_out
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_hinv
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_reflection_column_dual_isotropic
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_tau_e
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_tau_val
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_weyl_cell_apply_basis
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_wg_glev

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants.WeylGroupFacts
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
variable {k r : ℕ}
private lemma tau_tau_lemma (i : Fin (2 * r + k + 1)) : tau k r (tau k r i) = i := by
  have hi := i.isLt
  apply Fin.ext
  simp only [tau_val]
  split_ifs <;> omega
section Cases
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {z : Fin (2 * r + k + 1) → ℂ}
  {l : Fin r} {D : Set (Mx k r)} {f : Mx k r → E} {c : ℂ} {g₁ : Mx k r}
end Cases
end Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
end
end

set_option autoImplicit false
open Matrix
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants.WeylGroupFacts
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {z : Fin (2 * r + k + 1) → ℂ}
  {l : Fin r} {D : Set (Mx k r)} {f : Mx k r → E} {c : ℂ} {g₁ : Mx k r}
namespace Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
theorem _root_.solution (hz : inWb k r z) (hL : LeftEq k r z l.castSucc D f) (hc : c ≠ 0)
    (hg₁ : g₁ ∈ Glev k r l.succ) (hgD : w1 k r l c * g₁ ∈ D) :
    EH k r (esI k r l) (eI k r l) f (w1 k r l c * g₁) = 0 := by
  have hl := l.isLt
  have hg : w1 k r l c * g₁ ∈ Glev k r l.castSucc ∩ D := ⟨wg_glev l c hc hg₁, hgD⟩
  have hinv := glev_inv hg₁
  have hre := (glev_out hg₁ (eI k r l) (e_out l)).1
  have hces := (glev_out hg₁ (esI k r l) (es_out l)).2
  have hire := (glev_out hinv (eI k r l) (e_out l)).1
  have hA : ∀ p, (w1 k r l c * g₁) p (esI k r l) = if p = eI k r l then (star c)⁻¹ else 0 :=
    fun p => by
      rw [Matrix.mul_apply]
      simp only [hces, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [reflection_column_dual_isotropic]
  have hB : ∀ q, (g₁⁻¹ * w1 k r l (star c)) (eI k r l) q = if q = esI k r l then c⁻¹ else 0 :=
    fun q => by
      rw [Matrix.mul_apply]
      simp only [hire, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [weyl_cell_apply_basis, star_star]
  have hMe : ∀ p q,
      (w1 k r l c * g₁ * Matrix.single (esI k r l) (eI k r l) 1 * (w1 k r l c * g₁)⁻¹ : Mx k r) p q =
      (if p = eI k r l then (star c)⁻¹ else 0) * (if q = esI k r l then c⁻¹ else 0) := fun p q => by
    rw [ginv_eq hc, single_conj, hA, hB]
  have hS : InS k r l
      (w1 k r l c * g₁ * Matrix.single (esI k r l) (eI k r l) 1 * (w1 k r l c * g₁)⁻¹) := by
    intro p q hpq
    rw [hMe]
    by_cases hp : p = eI k r l
    · by_cases hq : q = esI k r l
      · exfalso
        apply hpq
        left
        subst hp
        subst hq
        exact ⟨rfl, show l.val < 2 * r + k - l.val by omega, le_refl _⟩
      · rw [if_neg hq, mul_zero]
    · rw [if_neg hp, zero_mul]
  rw [core hz hL hg (esI k r l) (eI k r l) hS, ell_form hz hS, ell_dag_form hz hS]
  have h1 : ∑ q, (w1 k r l c * g₁ * Matrix.single (esI k r l) (eI k r l) 1 * (w1 k r l c * g₁)⁻¹ : Mx k r)
      (eI k r l) q * fvec k r z l.succ q = 0 := by
    apply Finset.sum_eq_zero
    intro q _
    rw [hMe, if_pos rfl]
    by_cases hq : q = esI k r l
    · rw [hq, fvec_es hz l, mul_zero]
    · rw [if_neg hq, mul_zero, zero_mul]
  have h2 : ∑ q, star ((w1 k r l c * g₁ * Matrix.single (esI k r l) (eI k r l) 1 *
      (w1 k r l c * g₁)⁻¹ : Mx k r) (tau k r q) (esI k r l)) * WeylGroupFacts.sgn k r q * fvec k r z l.succ q = 0 := by
    apply Finset.sum_eq_zero
    intro q _
    by_cases hq : q = esI k r l
    · rw [hq, fvec_es hz l, mul_zero]
    · rw [hMe, if_neg (fun h => hq (by rw [← tau_tau_lemma q, h, tau_e])), zero_mul, star_zero,
        zero_mul, zero_mul]
  rw [h1, h2, star_zero, add_zero, zero_smul]
end Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
