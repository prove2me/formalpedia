-- Prove2me | solution 1 for CompanionTheory.D.Upq.QuotSetU.unipotent_radical_contracting
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:28:52.374154+00:00
-- url     : https://prove2.me/submissions/0d9c9a7a-4be3-48a2-916f-94b9d45e239c

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_SGroup
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_NContract
import Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_expo_lt
import Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_dvec_mul_inv
import Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_cdiag_mul
import Theorems.Thm_P2M_CompanionTheory_D_Upq_QuotSetU_cdiag_mul__260c206f0917
import Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_cdiag_inv
import Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_conj_apply
import Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_cdiag_normalises
import Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_norm_dvec_mul
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_mem_Nset_iff
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_n_ut


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.QuotSetU
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW
variable {k r : ℕ}
local notation "𝕄" => Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ
variable {z : Fin (2 * r + k + 1) → ℂ}
namespace CompanionTheory.D.Upq.QuotSetU
theorem _root_.solution : NContract := by
  intro k r z _hz n hn ε hε
  set M : ℝ := ∑ i, ∑ j, ‖n i j‖ with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  have hnM : ∀ i j, ‖n i j‖ ≤ M := fun i j =>
    (Finset.single_le_sum (f := fun j => ‖n i j‖) (fun j _ => norm_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, ‖n i j‖)
        (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ i))
  set t : ℝ := min 1 (ε / (M + 1)) with htdef
  have ht0 : 0 < t := lt_min one_pos (div_pos hε (by linarith))
  have ht1 : t ≤ 1 := min_le_left _ _
  have htM : t * M ≤ ε := by
    have h1 : t ≤ ε / (M + 1) := min_le_right _ _
    have h2 : ε / (M + 1) * M ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith
    exact (mul_le_mul_of_nonneg_right h1 hM0).trans h2
  refine ⟨cdiag k r t, ⟨⟨cdiag k r t, cdiag k r t⁻¹, cdiag_mul ht0.ne', cdiag_mul' ht0.ne'⟩, rfl⟩,
    cdiag_normalises ht0.ne', fun i j => ?_⟩
  rw [cdiag_inv ht0.ne', Matrix.sub_apply, conj_apply, Matrix.one_apply]
  by_cases hji : j.val ≤ i.val
  · rw [n_ut hn i j hji]
    split_ifs with h
    · subst h; rw [mul_one, dvec_mul_inv ht0.ne', sub_self, norm_zero]; exact hε.le
    · rw [mul_zero, zero_mul, sub_zero, norm_zero]; exact hε.le
  · have hij : i.val < j.val := by omega
    have hne : i ≠ j := by intro e; subst e; omega
    rw [if_neg hne, sub_zero]
    by_cases hW : inW k r i ∧ inW k r j
    · have hn' := ((mem_Nset_iff n).1 hn).2 i j hW.2.2 (by unfold inW at hW; omega)
      rw [hn', if_neg hne, mul_zero, zero_mul, norm_zero]; exact hε.le
    · rw [norm_dvec_mul t ht0]
      have hexp := expo_lt (k := k) (r := r) hij hW
      have h1 : t ^ (expo k r i - expo k r j) ≤ t ^ (1 : ℤ) :=
        zpow_le_zpow_right_of_le_one₀ ht0 ht1 (by omega)
      rw [zpow_one] at h1
      calc t ^ (expo k r i - expo k r j) * ‖n i j‖ ≤ t * M :=
            mul_le_mul h1 (hnM i j) (norm_nonneg _) ht0.le
        _ ≤ ε := htM
end CompanionTheory.D.Upq.QuotSetU
