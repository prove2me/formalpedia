-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.toZMod_ne_zero_of_mem_mu
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:36:06.008807+00:00
-- url     : https://prove2.me/submissions/677cc121-7e77-4d27-a812-d716125bc30b

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_prime_sub_one_pos
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_mem_mu_iff_pow_eq_one
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_toZMod_eq_zero_iff_norm_lt_one

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
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution {d : ℤ_[l]} (hd : d ∈ mu l) : PadicInt.toZMod d ≠ 0 := by
  intro h
  rw [toZMod_eq_zero_iff_norm_lt_one] at h
  have hlt : ‖d‖ ^ (l - 1) < 1 := pow_lt_one₀ (norm_nonneg _) h (prime_sub_one_pos l).ne'
  rw [← norm_pow, (mem_mu_iff_pow_eq_one l).mp hd, norm_one] at hlt
  exact lt_irrefl _ hlt
end Formalism.CohomologicalDescent.HeightDescentMinors
