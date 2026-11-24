-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qn_off_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:42.435943+00:00
-- url     : https://prove2.me/submissions/c8c0669b-1e82-4bf9-9585-576d01d8d6c1

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnPtEmpty
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
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {n : ℕ} (ν : Fin n → ℕ) (m e : Fin n × Fin n →₀ ℕ) (hm : LowerTri m) (he : LowerTri e)
    (hmc : ∀ t : Fin n, ∑ a : Fin n, m (a, t) = ν t) (hec : ∀ t : Fin n, ∑ a : Fin n, e (a, t) = ν t)
    (h : qn_off m = qn_off e) : m = e := by
  classical
  have hoff : ∀ a c : Fin n, a ≠ c → m (a, c) = e (a, c) := by
    intro a c hac
    rcases lt_or_gt_of_ne hac with h1 | h1
    · rw [hm a c h1, he a c h1]
    · have := DFunLike.congr_fun h (a, c)
      simpa [qn_off, Finsupp.filter_apply, h1] using this
  ext ⟨a, c⟩
  by_cases hac : a = c
  · subst hac
    have h1 := hmc a
    have h2 := hec a
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)] at h1 h2
    have h3 : ∑ x ∈ Finset.univ.erase a, m (x, a) = ∑ x ∈ Finset.univ.erase a, e (x, a) :=
      Finset.sum_congr rfl fun x hx => hoff x a (Finset.ne_of_mem_erase hx)
    omega
  · exact hoff a c hac
end Formalism.InvariantFactorPaths.ColumnFamilies
