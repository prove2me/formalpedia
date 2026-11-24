-- Prove2me | solution 1 for Formalism.CohomologicalDescent.leastCongruentPos_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:32:55.29963+00:00
-- url     : https://prove2.me/submissions/6b3de901-a14b-441d-8263-c4b8033dfc3a

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_Statement
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LabelSumNeedsLeFalse

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent
open Classical
namespace Formalism.CohomologicalDescent
theorem _root_.solution {l : ℕ} (hl : 0 < l) (D : ℤ) (hD : 0 ≤ D) :
    1 ≤ d0 l D ∧ (l : ℤ) ∣ D - (d0 l D : ℤ) := by
  have hne : ({d : ℕ | 1 ≤ d ∧ (l : ℤ) ∣ D - (d : ℤ)} : Set ℕ).Nonempty := by
    refine ⟨D.toNat + l, ?_⟩
    simp only [Set.mem_ofPred_eq]
    refine ⟨by omega, ?_⟩
    have e : D - ((D.toNat + l : ℕ) : ℤ) = -(l : ℤ) := by
      push_cast
      rw [Int.toNat_of_nonneg hD]
      ring
    rw [e]
    exact (dvd_neg).mpr dvd_rfl
  unfold d0
  exact Nat.sInf_mem hne
end Formalism.CohomologicalDescent
