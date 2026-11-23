-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.r2_inverse_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:13.093341+00:00
-- url     : https://prove2.me/submissions/c569f664-3326-4ef5-abbb-a61900b47d19

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_binomialAction_binomialSeriesSubOne
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_prime_sub_one_pos
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_mem_mu_iff_pow_eq_one
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_act_finset_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
variable (l : ℕ) [Fact l.Prime]
variable (O : Type) [CommRing O] [Algebra ℤ_[l] O]
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution : DivisibilityInvariant := by
  intro l _ O _ _ d hd
  have hd1 := (mem_mu_iff_pow_eq_one l).mp hd
  have hd0 : d ≠ 0 := by
    intro h
    rw [h, zero_pow (prime_sub_one_pos l).ne'] at hd1
    exact zero_ne_one hd1
  rw [pi0, act_finset_prod, Finset.prod_congr rfl (fun e _ => binomialAction_binomialSeriesSubOne l O d e)]
  apply Finset.prod_nbij (fun e => e * d)
  · intro e he
    rw [mem_mu_iff_pow_eq_one, mul_pow, (mem_mu_iff_pow_eq_one l).mp he, hd1, one_mul]
  · intro e _ e' _ h
    exact mul_right_cancel₀ hd0 h
  · intro e he
    refine ⟨e * d ^ (l - 1 - 1), ?_, ?_⟩
    · have he1 := (mem_mu_iff_pow_eq_one l).mp he
      show e * d ^ (l - 1 - 1) ∈ mu l
      rw [mem_mu_iff_pow_eq_one, mul_pow, he1, one_mul, ← pow_mul, Nat.mul_comm, pow_mul, hd1, one_pow]
    · show e * d ^ (l - 1 - 1) * d = e
      rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel (prime_sub_one_pos l), hd1, mul_one]
  · intro e _; rfl
end Formalism.CohomologicalDescent.HeightDescentMinors
