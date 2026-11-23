-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.not_pow_sum_dvd_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:33.704476+00:00
-- url     : https://prove2.me/submissions/a5c0bf66-30b8-46d9-90d8-e269e4027829

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_not_pow_dvd_mul_of_not_pow_dvd

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
variable {R : Type} [CommRing R]
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution [IsDomain R] {π : R} (hπ : Prime π) {κ : Type} (s : Finset κ)
    (v : κ → ℕ) (y : κ → R) (h : ∀ r ∈ s, ¬ π ^ (v r + 1) ∣ y r) :
    ¬ π ^ (∑ r ∈ s, v r + 1) ∣ ∏ r ∈ s, y r := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro hd
    exact hπ.not_isUnit (isUnit_of_dvd_one (by simpa using hd))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact not_pow_dvd_mul_of_not_pow_dvd hπ (h a (Finset.mem_insert_self _ _))
      (ih fun r hr => h r (Finset.mem_insert_of_mem hr))
end Formalism.CohomologicalDescent.HeightDescentMinors
