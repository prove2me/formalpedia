-- Prove2me | solution 1 for Formalism.CohomologicalDescent.sum_filter_block_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:40:18.824202+00:00
-- url     : https://prove2.me/submissions/c885318f-1fdd-439e-9203-a7d120ded19c

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_WEChain
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ContentLinkageHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightExchangeBoundHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightExchangeChainHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open Formalism Formalism.CohomologicalDescent
namespace Formalism.CohomologicalDescent
theorem _root_.solution (k j t q : ℕ) (U : Fin (k + j + t + q) → ℤ) (b : ℤ)
    (hblock : ∀ a : Fin (k + j + t + q), k + j ≤ (a : ℕ) → (a : ℕ) < k + j + t →
      U a = b + ((k + j + t - 1 - (a : ℕ) : ℕ) : ℤ)) :
    ∑ a ∈ Finset.univ.filter
        (fun a : Fin (k + j + t + q) => k + j ≤ (a : ℕ) ∧ (a : ℕ) < k + j + t), U a =
      ∑ s : Fin t, (b + ((s : ℕ) : ℤ)) := by
  refine Finset.sum_bij'
    (fun a ha => (⟨k + j + t - 1 - (a : ℕ), by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      omega⟩ : Fin t))
    (fun s _ => (⟨k + j + t - 1 - (s : ℕ), by
      have := s.isLt
      omega⟩ : Fin (k + j + t + q))) ?_ ?_ ?_ ?_ ?_
  · intro a _
    exact Finset.mem_univ _
  · intro s _
    have := s.isLt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    ext
    simp only
    omega
  · intro s _
    have := s.isLt
    ext
    simp only
    omega
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    rw [hblock a ha.1 ha.2]
end Formalism.CohomologicalDescent
