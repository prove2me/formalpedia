-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.q_dvd_q_zero_of_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:50:00.349906+00:00
-- url     : https://prove2.me/submissions/eaaf7588-1dc5-43ca-9e0b-bd0dc4ecbdde

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_dvd_prod_sub_prod_of_dvd_sub
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_q_dvd_prod_sub_l
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_q_dvd_binomialSeriesSubOne_sub_pow
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_padicInt_eq_digit_add_mul
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_prod_mu_toZMod_val_eq_prod_Ioo

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
theorem _root_.solution (ha : ActLaws) (hm : MuFacts) (hq : QMul) (hl2 : l ≠ 2) :
    q l ℤ_[l] ∣ q0 l ℤ_[l] := by
  have h1 : q l ℤ_[l] ∣ ∏ d ∈ mu l, br l ℤ_[l] d -
      ∏ d ∈ mu l, ((1 + X : ℤ_[l]⟦X⟧) ^ (PadicInt.toZMod d).val - 1) := by
    apply dvd_prod_sub_prod_of_dvd_sub
    intro d _
    obtain ⟨e, he⟩ := padicInt_eq_digit_add_mul l d
    have h := q_dvd_binomialSeriesSubOne_sub_pow l ha hq (PadicInt.toZMod d).val e
    rwa [← he] at h
  rw [prod_mu_toZMod_val_eq_prod_Ioo l hm (fun c => (1 + X : ℤ_[l]⟦X⟧) ^ c - 1)] at h1
  have h2 := dvd_add h1 (q_dvd_prod_sub_l l hq hl2)
  have e : q0 l ℤ_[l] = (∏ d ∈ mu l, br l ℤ_[l] d -
      ∏ c ∈ Finset.Ioo 0 l, ((1 + X : ℤ_[l]⟦X⟧) ^ c - 1)) +
      ((∏ c ∈ Finset.Ioo 0 l, ((1 + X : ℤ_[l]⟦X⟧) ^ c - 1)) - C (l : ℤ_[l])) := by
    rw [q0, pi0]
    ring
  rw [e]
  exact h2
end Formalism.CohomologicalDescent.HeightDescentMinors
