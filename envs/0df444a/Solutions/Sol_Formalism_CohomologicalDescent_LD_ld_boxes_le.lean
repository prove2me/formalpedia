-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.ld_boxes_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:43:39.997689+00:00
-- url     : https://prove2.me/submissions/ceb8d85d-049a-4d46-8dcb-b21306bb49b1

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
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
theorem _root_.solution (p w i q : ℕ) (lam2 tau : Fin q → ℕ) (htau : tau ∈ shapes p w i lam2) (c : ℤ) :
    boxesOfContent lam2 tau c ≤ p := by
  simp only [shapes, Finset.mem_filter, Fintype.mem_piFinset] at htau
  obtain ⟨-, hanti, -, hcol, -⟩ := htau
  unfold boxesOfContent
  rcases (Finset.univ.filter fun a : Fin q =>
      (lam2 a : ℤ) ≤ c + (a.val : ℤ) ∧ c + (a.val : ℤ) < (tau a : ℤ)).eq_empty_or_nonempty with hS | hS
  · rw [hS]; simp
  · have hb := Finset.max'_mem _ hS
    have hb' := (Finset.mem_filter.mp hb).2
    have hj0 : 0 ≤ c + (((Finset.univ.filter fun a : Fin q =>
        (lam2 a : ℤ) ≤ c + (a.val : ℤ) ∧ c + (a.val : ℤ) < (tau a : ℤ)).max' hS).val : ℤ) :=
      le_trans (Int.natCast_nonneg _) hb'.1
    obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le hj0
    have hjt : j < tau ((Finset.univ.filter fun a : Fin q =>
        (lam2 a : ℤ) ≤ c + (a.val : ℤ) ∧ c + (a.val : ℤ) < (tau a : ℤ)).max' hS) := by omega
    refine le_trans (Finset.card_le_card ?_) (hcol _ j hjt)
    intro a ha
    have ha' := (Finset.mem_filter.mp ha).2
    have hab := Finset.le_max' _ a ha
    have hab' : (a.val : ℤ) ≤ (((Finset.univ.filter fun a : Fin q =>
        (lam2 a : ℤ) ≤ c + (a.val : ℤ) ∧ c + (a.val : ℤ) < (tau a : ℤ)).max' hS).val : ℤ) := by
      exact_mod_cast hab
    have htb := hanti a _ hab
    simp only [colLen, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> omega
end Formalism.CohomologicalDescent.LD
