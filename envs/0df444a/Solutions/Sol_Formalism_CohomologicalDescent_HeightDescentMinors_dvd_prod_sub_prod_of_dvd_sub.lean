-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.dvd_prod_sub_prod_of_dvd_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:31:35.022076+00:00
-- url     : https://prove2.me/submissions/3f128b03-23d6-489e-8a47-d23df113bc2c

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors

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
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution {R ι : Type} [CommRing R] (x : R) (s : Finset ι) (F G : ι → R)
    (h : ∀ i ∈ s, x ∣ F i - G i) : x ∣ ∏ i ∈ s, F i - ∏ i ∈ s, G i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have e : F a * ∏ i ∈ s, F i - G a * ∏ i ∈ s, G i =
        (F a - G a) * ∏ i ∈ s, F i + G a * (∏ i ∈ s, F i - ∏ i ∈ s, G i) := by ring
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_right h2 _)
end Formalism.CohomologicalDescent.HeightDescentMinors
