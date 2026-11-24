-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.ell_dag_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:14:25.803958+00:00
-- url     : https://prove2.me/submissions/54d01c56-0b69-40eb-a96c-ea7576094574

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_HasDerivAtPhase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_LeftMultiplicationRule
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_ell_form
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_sgn_e
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_tau_e
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_tau_val

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
private lemma hpk_eq_lemma (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = tau k r i then WeylGroupFacts.sgn k r i else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  unfold Hpk WeylGroupFacts.sgn
  simp only [Fin.ext_iff, tau_val]
  split_ifs <;> first | rfl | omega | norm_num
private lemma tau_tau_lemma (i : Fin (2 * r + k + 1)) : tau k r (tau k r i) = i := by
  have hi := i.isLt
  apply Fin.ext
  simp only [tau_val]
  split_ifs <;> omega
private lemma sgn_tau_lemma (i : Fin (2 * r + k + 1)) : WeylGroupFacts.sgn k r (tau k r i) = WeylGroupFacts.sgn k r i := by
  have hi := i.isLt
  unfold WeylGroupFacts.sgn
  simp only [tau_val]
  split_ifs <;> first | rfl | omega
private lemma hpk_col_lemma (x y : Fin (2 * r + k + 1)) :
    Hpk k r x y = if x = tau k r y then WeylGroupFacts.sgn k r y else 0 := by
  rw [hpk_eq_lemma]
  by_cases h : x = tau k r y
  · subst h
    simp [tau_tau_lemma, sgn_tau_lemma]
  · rw [if_neg h, if_neg]
    intro h'
    apply h
    rw [h', tau_tau_lemma]
private lemma hpk_mul_conjTranspose_mul_hpk_apply (M : Mx k r) (p q : Fin (2 * r + k + 1)) :
    (Hpk k r * Mᴴ * Hpk k r) p q =
      WeylGroupFacts.sgn k r p * star (M (tau k r q) (tau k r p)) * WeylGroupFacts.sgn k r q := by
  rw [Matrix.mul_apply]
  have inner : ∀ y, (Hpk k r * Mᴴ) p y = WeylGroupFacts.sgn k r p * star (M y (tau k r p)) := fun y => by
    rw [Matrix.mul_apply]
    simp only [hpk_eq_lemma, Matrix.conjTranspose_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [inner, hpk_col_lemma, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
private lemma sp_of_sp_tau {l : Fin r} {p q : Fin (2 * r + k + 1)}
    (h : SP k r l (tau k r q) (tau k r p)) : SP k r l p q := by
  have hl := l.isLt
  have hp := p.isLt
  have hq := q.isLt
  have e1 := tau_val (k := k) (r := r) p
  have e2 := tau_val (k := k) (r := r) q
  unfold SP at h ⊢
  split_ifs at e1 e2 <;> omega
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
namespace Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {l : Fin r} {M : Mx k r}
    (hM : InS k r l M) : ell k r z (Hpk k r * Mᴴ * Hpk k r) =
      ∑ q, star (M (tau k r q) (esI k r l)) * WeylGroupFacts.sgn k r q * fvec k r z l.succ q := by
  have hN : InS k r l (Hpk k r * Mᴴ * Hpk k r) := by
    intro p q hpq
    rw [hpk_mul_conjTranspose_mul_hpk_apply, hM _ _ (fun h => hpq (sp_of_sp_tau h)), star_zero, mul_zero, zero_mul]
  rw [ell_form hz hN]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hpk_mul_conjTranspose_mul_hpk_apply, tau_e, sgn_e, one_mul]
end Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
