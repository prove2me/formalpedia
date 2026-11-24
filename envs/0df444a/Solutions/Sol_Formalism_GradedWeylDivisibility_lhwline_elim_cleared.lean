-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lhwline_elim_cleared
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:16:41.770703+00:00
-- url     : https://prove2.me/submissions/ba7820d4-a4a6-4f99-bc77-75b56be8c4e7

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_elim_inv
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_step_cleared
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_pivot_ne
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_minor_RInv
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_minor_CInv
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
variable {K : Type} [Field K] {r n : ℕ}
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution [Infinite K] (x : Fin r × Fin n → K)
    (hx : ∀ (s : ℕ) (hr : s + 1 ≤ r) (hn : s + 1 ≤ n), eval x (lpMinor K (s + 1) hr hn) ≠ 0) :
    ∀ k, k ≤ min r n → lhwline_cleared k (lhwline_elim k x) := by
  intro k
  induction k with
  | zero =>
    intro _ a j _ h
    simp at h
  | succ k ih =>
    intro hk
    have hr : k < r := by have := min_le_left r n; omega
    have hn : k < n := by have := min_le_right r n; omega
    have hy := ih (by omega)
    have hel : lhwline_elim (k + 1) x = highestWeightLineUpdate ⟨k, hr⟩ ⟨k, hn⟩ (lhwline_elim k x) := by
      simp only [lhwline_elim]
      rw [dif_pos ⟨hr, hn⟩]
    rw [hel]
    apply lhwline_step_cleared k hr hn _ hy
    apply lhwline_pivot_ne k hr hn _ hy
    have hinv := lhwline_elim_inv (fun z : Fin r × Fin n → K => eval z (lpMinor K (k + 1) hr hn))
      (lhwline_minor_RInv _ _ _) (lhwline_minor_CInv _ _ _) k x
    intro h0
    exact hx k hr hn (hinv.symm.trans h0)
end Formalism.GradedWeylDivisibility
