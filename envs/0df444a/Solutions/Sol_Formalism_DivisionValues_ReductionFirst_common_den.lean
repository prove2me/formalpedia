-- Prove2me | solution 1 for Formalism.DivisionValues.ReductionFirst.common_den
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:24:30.905842+00:00
-- url     : https://prove2.me/submissions/f44c89b5-396a-406f-b2ef-7cc387dff76b

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SelectionLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaFirst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Matrix
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.ReductionFirst
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues.ReductionFirst
theorem _root_.solution {w : HeightOneSpectrum (𝓞 K)} {ι : Type*} (S : Finset ι) (x : ι → K)
    (h : ∀ k ∈ S, InS w (x k)) : ∃ s ∈ Tw w, ∀ k ∈ S, ∃ r : 𝓞 K, (s : K) * x k = r := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, (Tw w).one_mem, by simp⟩
  | @insert a S ha ih =>
    obtain ⟨t, ht, hS⟩ := ih (fun k hk => h k (Finset.mem_insert_of_mem hk))
    obtain ⟨s, hs, r, hr⟩ := h a (Finset.mem_insert_self a S)
    refine ⟨s * t, (Tw w).mul_mem hs ht, ?_⟩
    intro k hk
    rcases Finset.mem_insert.1 hk with rfl | hk
    · exact ⟨t * r, by show (s : K) * (t : K) * x k = (t : K) * (r : K); linear_combination (t : K) * hr⟩
    · obtain ⟨r', hr'⟩ := hS k hk
      exact ⟨s * r', by show (s : K) * (t : K) * x k = (s : K) * (r' : K); linear_combination (s : K) * hr'⟩
end Formalism.DivisionValues.ReductionFirst
