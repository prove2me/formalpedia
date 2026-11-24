-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.ld_sym_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:18:04.123205+00:00
-- url     : https://prove2.me/submissions/a6172add-056c-4886-a88d-540422abc794

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_sym_hw
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_sym_step
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_weylRowDivStable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution (q w : ℕ) (μ : Fin (1 + q) → ℕ) (S : Finset (Fin (1 + q))) (hz : ldZ q ∉ S)
    (hS : ∑ a ∈ S, μ a ≤ w) :
    ∃ c : ℕ, c ∣ w.descFactorial (∑ a ∈ S, μ a) ∧
      (c : ℤ) • ldSv q w μ S ∈ weyl ℤ (1 + q) (1 + q) le_rfl (blockWt 1 q w fun _ => 0) := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨1, by simp, ?_⟩
    have h0 : ldSv q w μ ∅ = hw ℤ (le_refl (1 + q)) (blockWt 1 q w (fun _ => 0)) := by
      rw [ld_sym_hw]
      simp [ldSv]
    rw [h0, Nat.cast_one, one_smul]
    exact Submodule.subset_span ⟨[], rfl⟩
  | insert a S ha ih =>
    have hz' : ldZ q ∉ S := fun h => hz (Finset.mem_insert_of_mem h)
    rw [Finset.sum_insert ha] at hS
    obtain ⟨c, hc, hmem⟩ := ih hz' (by omega)
    refine ⟨c * (w - ∑ b ∈ S, μ b).choose (μ a), ?_, ?_⟩
    · rw [Finset.sum_insert ha, add_comm (μ a)]
      have h1 := Nat.descFactorial_mul_descFactorial (n := w) (k := ∑ b ∈ S, μ b)
        (m := ∑ b ∈ S, μ b + μ a) (Nat.le_add_right _ _)
      rw [Nat.add_sub_cancel_left] at h1
      rw [← h1, mul_comm]
      refine Nat.mul_dvd_mul ?_ hc
      rw [Nat.descFactorial_eq_factorial_mul_choose]
      exact Dvd.intro_left _ rfl
    · have h2 := weylRowDivStable ℤ (1 + q) (1 + q) le_rfl (blockWt 1 q w fun _ => 0) a (ldZ q) (μ a) _ hmem
      rw [rowDiv_smul, ld_sym_step q w μ S a ha hz', smul_smul] at h2
      push_cast
      exact h2
end Formalism.CohomologicalDescent.LD
