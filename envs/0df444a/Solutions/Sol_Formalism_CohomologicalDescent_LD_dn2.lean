-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.dn2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:04:46.928075+00:00
-- url     : https://prove2.me/submissions/70976d65-5f57-46ec-a06d-a8381be43cee

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_mu_one
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
theorem _root_.solution : Dn2 := by
  intro p w y i hp h
  unfold Dn
  have e1 : ∀ k ∈ Finset.range (1 + w + i), ((w : ℤ) - ((k : ℤ) - ((1 : ℕ) : ℤ))) ^
      mu p w i (fun _ : Fin 1 => y) ((k : ℤ) - ((1 : ℕ) : ℤ)) =
      if (y : ℤ) ≤ (k : ℤ) - 1 ∧ (k : ℤ) - 1 < (y : ℤ) + (i : ℤ) then (w : ℤ) - ((k : ℤ) - 1) else 1 := by
    intro k _
    rw [ld_mu_one p w y i hp h]
    push_cast
    split_ifs <;> simp
  rw [Finset.prod_congr rfl e1, ← Finset.prod_filter]
  have e2 : (Finset.range (1 + w + i)).filter
      (fun k : ℕ => (y : ℤ) ≤ (k : ℤ) - 1 ∧ (k : ℤ) - 1 < (y : ℤ) + (i : ℤ)) =
      (Finset.range i).image (fun j => j + y + 1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨_, h1, h2⟩
      exact ⟨k - y - 1, by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩
      push_cast
      omega
  rw [e2, Finset.prod_image (by intro a _ b _ hab; simpa using hab)]
  rw [← Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  push_cast
  omega
end Formalism.CohomologicalDescent.LD
