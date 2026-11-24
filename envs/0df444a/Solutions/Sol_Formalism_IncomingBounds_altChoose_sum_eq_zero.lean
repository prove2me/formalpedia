-- Prove2me | solution 1 for Formalism.IncomingBounds.altChoose_sum_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:10.507798+00:00
-- url     : https://prove2.me/submissions/08b3930f-d3cd-48ea-8950-8bf4c1e12af8

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_LevelTail
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_AltChooseSumEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset fwdDiff
open Formalism Formalism.IncomingBounds
namespace Formalism.IncomingBounds
theorem _root_.solution (D s y : ℕ) (hs : s ≤ D) :
    ∑ k ∈ range (D + 1 + 1), ((-1 : ℤ) ^ (D + 1 - k) * ((D + 1).choose k : ℤ)) *
      (((y + k).choose s : ℕ) : ℤ) = 0 := by
  have h := fwdDiff_iter_eq_sum_shift (1 : ℕ) (fun x ↦ (x.choose s : ℤ)) (D + 1) y
  have hz : (fwdDiff (1 : ℕ))^[D + 1] (fun x ↦ (x.choose s : ℤ) : ℕ → ℤ) y = 0 := by
    obtain ⟨k, hk⟩ : ∃ k, D + 1 = (k + 1) + s := ⟨D - s, by omega⟩
    rw [hk, Function.iterate_add_apply]
    have h0 := fwdDiff_iter_choose 0 s
    simp only [add_zero] at h0
    rw [h0]
    simp only [Nat.choose_zero_right, Nat.cast_one, Function.iterate_succ_apply, fwdDiff_const]
    rw [fwdDiff_iter_eq_sum_shift]
    simp
  rw [hz] at h
  simpa [smul_eq_mul] using h.symm
end Formalism.IncomingBounds
