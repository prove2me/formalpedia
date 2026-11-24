-- Prove2me | solution 1 for Formalism.CohomologicalDescent.shiftBound_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:40:17.377683+00:00
-- url     : https://prove2.me/submissions/45ec0574-10ce-44f5-81e1-ebe97b0aa5a7

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_StatementLW
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_MinorValuationBoundHolds

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
theorem _root_.solution : KapBound := by
  intro ι _ σ l h kap s hl hs hd i
  have : Nonempty ι := ⟨i⟩
  obtain ⟨j, hj⟩ := Finite.exists_max (fun x => |kap x|)
  have hL : (2 : ℤ) ≤ (l : ℤ) := by exact_mod_cast hl
  have h1 := hd (σ.symm j)
  have h2 := hs (σ.symm j)
  rw [Equiv.apply_symm_apply] at h1
  have h3 := abs_le.mp (hj (σ.symm j))
  have key : ((l : ℤ) - 1) * |kap j| ≤ (h : ℤ) := by
    rcases le_or_gt 0 (kap j) with hk | hk
    · rw [abs_of_nonneg hk] at h3 ⊢
      have e : ((l : ℤ) - 1) * kap j = (l : ℤ) * kap j - kap j := by ring
      rw [e]
      linarith [h1.2, h2.1, h3.2]
    · rw [abs_of_neg hk] at h3 ⊢
      have e : ((l : ℤ) - 1) * -kap j = -((l : ℤ) * kap j) + kap j := by ring
      rw [e]
      linarith [h1.1, h2.2, h3.1]
  have h4 : ((l : ℤ) - 1) * |kap i| ≤ ((l : ℤ) - 1) * |kap j| :=
    mul_le_mul_of_nonneg_left (hj i) (by linarith)
  exact le_trans h4 key
end Formalism.CohomologicalDescent
