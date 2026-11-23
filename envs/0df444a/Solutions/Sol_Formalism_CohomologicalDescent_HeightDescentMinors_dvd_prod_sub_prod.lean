-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.dvd_prod_sub_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:31:34.693924+00:00
-- url     : https://prove2.me/submissions/26fc7356-89a9-4386-9f83-49da89f041bf

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
theorem _root_.solution {R ι : Type} [CommRing R] (s : Finset ι) (a b : ι → R) (x : R)
    (h : ∀ i ∈ s, x ∣ a i - b i) : x ∣ ∏ i ∈ s, a i - ∏ i ∈ s, b i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert c s hc ih =>
    rw [Finset.prod_insert hc, Finset.prod_insert hc]
    have h1 := h c (Finset.mem_insert_self c s)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have e : a c * ∏ i ∈ s, a i - b c * ∏ i ∈ s, b i =
        (a c - b c) * ∏ i ∈ s, a i + b c * (∏ i ∈ s, a i - ∏ i ∈ s, b i) := by ring
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_right h2 _)
end Formalism.CohomologicalDescent.HeightDescentMinors
