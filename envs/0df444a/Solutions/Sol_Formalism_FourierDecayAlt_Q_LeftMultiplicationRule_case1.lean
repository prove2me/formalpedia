-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.case1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:14:14.922314+00:00
-- url     : https://prove2.me/submissions/83df875e-d9fe-4268-b2c8-bf401306ecaa

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_HasDerivAtPhase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_LeftMultiplicationRule
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_single_conj
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_hpkVec
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_ell_form
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_ell_dag_form
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_ginv_eq
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_e_out
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_es_out
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_core
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_glev_inv
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_glev_out
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_hinv
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_star_sgn
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_weyl_cell_apply_basis
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_weyl_cell_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_wg_glev


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
    (hg₁ : g₁ ∈ Glev k r l.succ) (hgD : w1 k r l c * g₁ ∈ D) (v : Fin (2 * r + k + 1))
    (hv : l.val < v.val ∧ v.val < 2 * r + k - l.val) :
    EH k r v (eI k r l) f (w1 k r l c * g₁) =
      (c⁻¹ * herm (Hpk k r) (g₁ *ᵥ bvec v) (fvec k r z l.succ)) • f (w1 k r l c * g₁) := by
  have hl := l.isLt
  have hg : w1 k r l c * g₁ ∈ Glev k r l.castSucc ∩ D := ⟨wg_glev l c hc hg₁, hgD⟩
  have hinv := glev_inv hg₁
  have hv1 : v ≠ eI k r l := fun h => by rw [h] at hv; exact e_out l hv
  have hv2 : v ≠ esI k r l := fun h => by rw [h] at hv; exact es_out l hv
  have hre := (glev_out hg₁ (eI k r l) (e_out l)).1
  have hres := (glev_out hg₁ (esI k r l) (es_out l)).1
  have h0e : g₁ (eI k r l) v = 0 := by rw [hre, if_neg (Ne.symm hv1)]
  have h0es : g₁ (esI k r l) v = 0 := by rw [hres, if_neg (Ne.symm hv2)]
  have hcol : ∀ p, (w1 k r l c * g₁) p v = g₁ p v := fun p => weyl_cell_mul_apply l c g₁ p v h0e h0es
  have hire := (glev_out hinv (eI k r l) (e_out l)).1
  have hB : ∀ q, (g₁⁻¹ * w1 k r l (star c)) (eI k r l) q = if q = esI k r l then c⁻¹ else 0 :=
    fun q => by
      rw [Matrix.mul_apply]
      simp only [hire, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [weyl_cell_apply_basis, star_star]
  have hMe : ∀ p q, (w1 k r l c * g₁ * Matrix.single v (eI k r l) 1 * (w1 k r l c * g₁)⁻¹ : Mx k r) p q =
      g₁ p v * (if q = esI k r l then c⁻¹ else 0) := fun p q => by
    rw [ginv_eq hc, single_conj, hcol, hB]
  have hS : InS k r l (w1 k r l c * g₁ * Matrix.single v (eI k r l) 1 * (w1 k r l c * g₁)⁻¹) := by
    intro p q hpq
    rw [hMe]
    by_cases hq : q = esI k r l
    · have hp : ¬ (l.val < p.val ∧ p.val < 2 * r + k - l.val) :=
        fun hp => hpq (Or.inr ⟨by rw [hq]; rfl, hp.1, hp.2⟩)
      rw [(glev_out hg₁ p hp).1 v, if_neg (fun (h : p = v) => hp (h ▸ hv)), zero_mul]
    · rw [if_neg hq, mul_zero]
  rw [core hz hL hg v (eI k r l) hS, ell_form hz hS, ell_dag_form hz hS]
  congr 1
  simp only [hMe, h0e, zero_mul, Finset.sum_const_zero, zero_add, eq_self_iff_true, if_true]
  unfold herm
  simp only [dotProduct, Pi.star_apply]
  simp only [hpkVec]
  simp only [Matrix.mulVec, dotProduct, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [star_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [star_mul', star_star, star_sgn]
  ring
end Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
