-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qn_interlaced_lowerTri
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:39.293802+00:00
-- url     : https://prove2.me/submissions/4a9910de-e225-4def-80de-25f3d22ba839

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LCassemLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnInterlacedLowerTri
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
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
open scoped MonomialOrder
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {r n : ℕ} (m : Fin r × Fin n →₀ ℕ) (h : Interlaced m) : LowerTri m := by
  have key : ∀ k : ℕ, ∀ s : Fin n, s.val = k → ∀ a : Fin r, a.val < k → m (a, s) = 0 := by
    intro k
    induction k with
    | zero =>
      intro s _ a ha
      omega
    | succ k ih =>
      intro s hs a ha
      have hl : k < n := by
        have := s.isLt
        omega
      have hI := h ⟨k, hl⟩ s (by simp [hs]) a
      have hR : (∑ b : Fin r with b < a, m (b, (⟨k, hl⟩ : Fin n))) = 0 := by
        apply Finset.sum_eq_zero
        intro b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
        have hba : b.val < a.val := hb
        exact ih ⟨k, hl⟩ rfl b (by omega)
      rw [hR, add_zero, Nat.le_zero, Finset.sum_eq_zero_iff] at hI
      exact hI a (by simp)
  intro a s has
  exact key s.val s rfl a has
end Formalism.InvariantFactorPaths.ColumnFamilies
