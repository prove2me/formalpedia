-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.case2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:14:16.092525+00:00
-- url     : https://prove2.me/submissions/1e530103-89af-43dd-a0d8-9e18b1fe1e68

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_HasDerivAtPhase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_LeftMultiplicationRule
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_single_conj
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_ell_form
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_ell_dag_form
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_ginv_eq
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_e_out
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_es_out
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_core
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_glev_inv
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_glev_out
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_hinv
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_mul_weyl_cell_apply
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_reflection_column_dual_isotropic
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
    EH k r (esI k r l) v f (w1 k r l c * g₁) =
      ((star c)⁻¹ * (g₁⁻¹ *ᵥ fvec k r z l.succ) v) • f (w1 k r l c * g₁) := by
  have hl := l.isLt
  have hg : w1 k r l c * g₁ ∈ Glev k r l.castSucc ∩ D := ⟨wg_glev l c hc hg₁, hgD⟩
  have hinv := glev_inv hg₁
  have hv1 : v ≠ eI k r l := fun h => by rw [h] at hv; exact e_out l hv
  have hv2 : v ≠ esI k r l := fun h => by rw [h] at hv; exact es_out l hv
  have hces := (glev_out hg₁ (esI k r l) (es_out l)).2
  have hice := (glev_out hinv (eI k r l) (e_out l)).2
  have hices := (glev_out hinv (esI k r l) (es_out l)).2
  have hA : ∀ p, (w1 k r l c * g₁) p (esI k r l) = if p = eI k r l then (star c)⁻¹ else 0 :=
    fun p => by
      rw [Matrix.mul_apply]
      simp only [hces, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [reflection_column_dual_isotropic]
  have h0 : g₁⁻¹ v (esI k r l) = 0 := by rw [hices, if_neg hv2]
  have hB : ∀ q, (g₁⁻¹ * w1 k r l (star c)) v q = g₁⁻¹ v q := fun q =>
    mul_weyl_cell_apply l (star c) g₁⁻¹ v q (by rw [hice, if_neg hv1]) h0
  have hMe : ∀ p q, (w1 k r l c * g₁ * Matrix.single (esI k r l) v 1 * (w1 k r l c * g₁)⁻¹ : Mx k r) p q =
      (if p = eI k r l then (star c)⁻¹ else 0) * g₁⁻¹ v q := fun p q => by
    rw [ginv_eq hc, single_conj, hA, hB]
  have hS : InS k r l (w1 k r l c * g₁ * Matrix.single (esI k r l) v 1 * (w1 k r l c * g₁)⁻¹) := by
    intro p q hpq
    rw [hMe]
    by_cases hp : p = eI k r l
    · have hq : ¬ (l.val < q.val ∧ q.val < 2 * r + k - l.val) :=
        fun hq => hpq (Or.inl ⟨by rw [hp]; rfl, hq.1, le_of_lt hq.2⟩)
      rw [(glev_out hinv q hq).2 v, if_neg (fun (h : v = q) => hq (h ▸ hv)), mul_zero]
    · rw [if_neg hp, zero_mul]
  rw [core hz hL hg (esI k r l) v hS, ell_form hz hS, ell_dag_form hz hS]
  congr 1
  simp only [hMe, h0, mul_zero, star_zero, zero_mul, Finset.sum_const_zero, add_zero, eq_self_iff_true,
    if_true]
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  ring
end Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
