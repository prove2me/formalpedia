-- Prove2me | solution 1 for Bl.general_b_fact_left_tail.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:41.628524+00:00
-- url     : https://prove2.me/submissions/6b107083-52c8-4c06-ad38-e20a02c18308

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftTail_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Matrix
open Bl Bl.general_b_fact_left_tail
variable {F : Type} [Field F] [NumberField F]
namespace Bl.general_b_fact_left_tail
theorem _root_.solution (g : ℕ) (hg : g.Prime) : ∃ v : HeightOneSpectrum (𝓞 F), (g : 𝓞 F) ∈ v.asIdeal := by
  have hP : (Ideal.span {(g : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hg.ne_zero)).2 (Nat.prime_iff_prime_int.mp hg)
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 F)
    (Ideal.span {(g : ℤ)}) ⊥ (by
      rw [Ideal.comap_bot_of_injective _ (algebraMap ℤ (𝓞 F)).injective_int]
      exact bot_le)
  have hgQ : (g : 𝓞 F) ∈ Q := by
    have h1 : (g : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 F)) := by
      rw [hQc]
      exact Ideal.subset_span rfl
    simpa using h1
  refine ⟨⟨Q, hQ, ?_⟩, hgQ⟩
  intro h
  rw [h] at hgQ
  have h0 : (g : 𝓞 F) = 0 := (Ideal.mem_bot).1 hgQ
  exact hg.ne_zero (by exact_mod_cast h0)
end Bl.general_b_fact_left_tail
