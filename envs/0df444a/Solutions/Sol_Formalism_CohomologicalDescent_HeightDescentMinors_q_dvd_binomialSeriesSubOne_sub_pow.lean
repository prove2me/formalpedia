-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.q_dvd_binomialSeriesSubOne_sub_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:02.941101+00:00
-- url     : https://prove2.me/submissions/73514896-6244-4699-a770-b4657d5bd24a

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_dvd_subst_self
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_hasSubst_one_add_X_pow_sub_one_alt
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_constantCoeff_binomialSeriesSubOne_eq_zero

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
theorem _root_.solution (ha : ActLaws) (hq : QMul) (c : ℕ) (e : ℤ_[l]) :
    q l ℤ_[l] ∣ br l ℤ_[l] ((c : ℤ_[l]) + (l : ℤ_[l]) * e) - ((1 + X) ^ c - 1) := by
  have h1 : br l ℤ_[l] (e * (l : ℤ_[l])) = phi l ℤ_[l] (br l ℤ_[l] e) := by
    obtain ⟨a1, _, _, a4, _⟩ := ha l ℤ_[l]
    rw [a4, a1]
  have h2 : ((1 + X) ^ l - 1 : ℤ_[l]⟦X⟧) ∣ br l ℤ_[l] (e * (l : ℤ_[l])) := by
    rw [h1]
    exact dvd_subst_self (hasSubst_one_add_X_pow_sub_one_alt l) (constantCoeff_binomialSeriesSubOne_eq_zero l ℤ_[l] e)
  rw [← (hq l ℤ_[l]).1] at h2
  obtain ⟨s, hs⟩ := h2
  have h3 : binomialSeries ℤ_[l] (e * (l : ℤ_[l])) = 1 + X * q l ℤ_[l] * s := by
    rw [← hs, br]
    ring
  refine ⟨(1 + X) ^ c * X * s, ?_⟩
  rw [br, binomialSeries_add, binomialSeries_nat, mul_comm (l : ℤ_[l]) e, h3]
  ring
end Formalism.CohomologicalDescent.HeightDescentMinors
