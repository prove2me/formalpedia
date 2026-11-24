-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:57:25.464399+00:00
-- url     : https://prove2.me/submissions/c6c4788b-8fa3-4327-bd8b-210abf265e87

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_MulApplyS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_ReflectionColumnDualIsotropic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_HasDerivAtPhase
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_hinv
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_hpart1_conj
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_hpart2_conj
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_hpart1_skew
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_hpart2_skew
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_inS_dag
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_rdV_left
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_phase_sum
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_ell_add
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_inS_add
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_inS_smul
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_inS_sub


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
namespace Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {z : Fin (2 * r + k + 1) → ℂ}
    (hz : inWb k r z) {l : Fin r} {D : Set (Mx k r)} {f : Mx k r → E} (hL : LeftEq k r z l.castSucc D f)
    {g : Mx k r} (hg : g ∈ Glev k r l.castSucc ∩ D) (a b : Fin (2 * r + k + 1))
    (hS : InS k r l (g * Matrix.single a b 1 * g⁻¹)) :
    EH k r a b f g = (ell k r z (g * Matrix.single a b 1 * g⁻¹) +
      star (ell k r z (Hpk k r * (g * Matrix.single a b 1 * g⁻¹)ᴴ * Hpk k r))) • f g := by
  have ell_sm : ∀ (c : ℂ) (M : Mx k r), ell k r z (c • M) = c * ell k r z M := by
    intro c M
    simp only [ell, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs <;> simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  set W := g * Matrix.single a b 1 * g⁻¹ with hW
  have hgU : g ∈ UH (Hpk k r) := by
    have h := hg.1
    simp only [Glev, Set.mem_setOf_eq] at h
    exact h.1
  have hp1 : hpart1 (Hpk k r) W = (1 / 2 : ℂ) • (W - Hpk k r * Wᴴ * Hpk k r) := by
    simp only [hpart1, hinv]
  have hp2 : hpart2 (Hpk k r) W = (1 / (2 * Complex.I) : ℂ) • (W + Hpk k r * Wᴴ * Hpk k r) := by
    simp only [hpart2, hinv]
  have hS1 : InS k r l (g * hpart1 (Hpk k r) (Matrix.single a b 1) * g⁻¹) := by
    rw [hpart1_conj hgU, ← hW, hp1]
    exact inS_smul _ (inS_sub hS (inS_dag hS))
  have hS2 : InS k r l (g * hpart2 (Hpk k r) (Matrix.single a b 1) * g⁻¹) := by
    rw [hpart2_conj hgU, ← hW, hp2]
    exact inS_smul _ (inS_add hS (inS_dag hS))
  have hk1 : Hpk k r * (g * hpart1 (Hpk k r) (Matrix.single a b 1) * g⁻¹)ᴴ * Hpk k r =
      -(g * hpart1 (Hpk k r) (Matrix.single a b 1) * g⁻¹) := by
    rw [hpart1_conj hgU]; exact hpart1_skew _
  have hk2 : Hpk k r * (g * hpart2 (Hpk k r) (Matrix.single a b 1) * g⁻¹)ᴴ * Hpk k r =
      -(g * hpart2 (Hpk k r) (Matrix.single a b 1) * g⁻¹) := by
    rw [hpart2_conj hgU]; exact hpart2_skew _
  have r1 := rdV_left hz hL hg _ hS1 hk1
  have r2 := rdV_left hz hL hg _ hS2 hk2
  rw [hpart1_conj hgU, ← hW] at r1
  rw [hpart2_conj hgU, ← hW] at r2
  show RdV (hpart1 (Hpk k r) (Matrix.single a b 1)) f g +
    Complex.I • RdV (hpart2 (Hpk k r) (Matrix.single a b 1)) f g = _
  rw [r1, r2, smul_smul, ← add_smul, hp1, hp2, ell_sm, ell_sm]
  congr 1
  have hsub : ell k r z (W - Hpk k r * Wᴴ * Hpk k r) = ell k r z W - ell k r z (Hpk k r * Wᴴ * Hpk k r) := by
    rw [sub_eq_add_neg, ell_add, ← neg_one_smul ℂ (Hpk k r * Wᴴ * Hpk k r), ell_sm]; ring
  rw [hsub, ell_add]
  exact phase_sum _ _
end Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
