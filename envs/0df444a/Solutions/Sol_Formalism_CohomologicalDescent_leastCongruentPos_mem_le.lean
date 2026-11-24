-- Prove2me | solution 1 for Formalism.CohomologicalDescent.leastCongruentPos_mem_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:36:56.828799+00:00
-- url     : https://prove2.me/submissions/4f1e8dc7-dbaa-44ff-a1f0-d2652d9fcc73

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_Statement
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse

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
theorem _root_.solution (l D : ℕ) (hD : 1 ≤ D) :
    1 ≤ d0 l (D : ℤ) ∧ (l : ℤ) ∣ (D : ℤ) - (d0 l (D : ℤ) : ℤ) ∧ d0 l (D : ℤ) ≤ D := by
  have hmem : D ∈ {d : ℕ | 1 ≤ d ∧ (l : ℤ) ∣ (D : ℤ) - (d : ℤ)} := ⟨hD, by simp⟩
  have hs := Nat.sInf_mem (⟨D, hmem⟩ : ({d : ℕ | 1 ≤ d ∧ (l : ℤ) ∣ (D : ℤ) - (d : ℤ)}).Nonempty)
  unfold d0
  exact ⟨hs.1, hs.2, Nat.sInf_le hmem⟩
end Formalism.CohomologicalDescent
