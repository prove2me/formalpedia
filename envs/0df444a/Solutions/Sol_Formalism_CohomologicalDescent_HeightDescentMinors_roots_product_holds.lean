-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.roots_product_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:56:19.303831+00:00
-- url     : https://prove2.me/submissions/b1a9b7f6-bd42-46fe-83b7-1e1032f8b74f

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_eq_zero_of_X_sub_C_dvd_C
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_linear_prime_holds

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
theorem _root_.solution : RootsProduct := by
  intro O _ _ I _ s c S m hI hinj hdvd
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hs := ih (fun b hb => hI b (Finset.mem_insert_of_mem hb))
      (hinj.mono (by intro x hx; exact Finset.mem_insert_of_mem hx))
      (fun b hb => hdvd b (Finset.mem_insert_of_mem hb))
    obtain ⟨m', hm'⟩ := hs
    have hp := linear_prime_holds O I (c a) (hI a (Finset.mem_insert_self a s))
    have hnd : ¬ (X - C (c a) : O⟦X⟧) ∣ (∏ b ∈ s, (X - C (c b))) ^ S := by
      intro h
      have h1 := hp.dvd_of_dvd_pow h
      obtain ⟨b, hb, hb2⟩ := (Prime.dvd_finsetProd_iff hp _).mp h1
      have h3 : (X - C (c a) : O⟦X⟧) ∣ C (c a - c b) := by
        have : (C (c a - c b) : O⟦X⟧) = (X - C (c b)) - (X - C (c a)) := by rw [map_sub]; ring
        rw [this]; exact dvd_sub hb2 dvd_rfl
      have h4 := eq_zero_of_X_sub_C_dvd_C I (c a) (hI a (Finset.mem_insert_self a s)) _ h3
      have h5 : a = b := hinj (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hb)
        (sub_eq_zero.mp h4)
      exact ha (h5 ▸ hb)
    have h6 : (X - C (c a) : O⟦X⟧) ^ S ∣ m' :=
      hp.pow_dvd_of_dvd_mul_left S hnd (hm' ▸ hdvd a (Finset.mem_insert_self a s))
    obtain ⟨m'', hm''⟩ := h6
    refine ⟨m'', ?_⟩
    rw [Finset.prod_insert ha, hm', hm'', mul_pow]; ring
end Formalism.CohomologicalDescent.HeightDescentMinors
