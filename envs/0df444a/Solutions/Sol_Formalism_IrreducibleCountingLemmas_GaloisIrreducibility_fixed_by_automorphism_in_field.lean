-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.fixed_by_automorphism_in_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:06:34.440909+00:00
-- url     : https://prove2.me/submissions/ef78940b-d535-4954-84bd-0ac90b634c02

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_EigenbasisOfDistinctRoots
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_FixedByAutomorphismInField
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_exists_algEquiv_extending

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution : FixedByAutInField := by
  intro F z hz hfix
  have hzF : IsAlgebraic F z := hz.tower_top F
  have hzA : z ∈ algebraicClosure F ℂ := (mem_algebraicClosure_iff).2 hzF
  have : IsGalois F (algebraicClosure F ℂ) := inferInstance
  obtain ⟨r, hr⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed
    (k := F) (K := algebraicClosure F ℂ) ⟨z, hzA⟩).2 (by
      intro σ₀
      obtain ⟨σ, hσ⟩ := exists_algEquiv_extending σ₀
      apply Subtype.ext
      rw [← hσ]
      exact hfix σ)
  have : (r : ℂ) = z := congrArg Subtype.val hr
  rw [← this]
  exact r.2
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
