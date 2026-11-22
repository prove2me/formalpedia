-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lhwline_mnu_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T18:39:10.295696+00:00
-- url     : https://prove2.me/submissions/d8ccd932-96f0-4db9-af55-279bfe66f708

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
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
theorem _root_.solution (hn : n ≤ r) (ν : Fin n → ℕ) (a : Fin r) (j : Fin n) :
    lhwline_mnu hn ν (a, j) = if a.val = j.val then ν j else 0 := by
  simp only [lhwline_mnu, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply]
  rw [Finset.sum_eq_single j]
  · by_cases h : a.val = j.val
    · have : Fin.castLE hn j = a := Fin.ext (by rw [Fin.coe_castLE]; exact h.symm)
      simp [this, h]
    · have : ¬ (Fin.castLE hn j, j) = (a, j) := by
        intro h'
        apply h
        rw [← (Prod.mk.inj h').1, Fin.coe_castLE]
      simp [this, h]
  · intro b _ hb
    rw [if_neg]
    intro h'
    exact hb (Prod.mk.inj h').2
  · simp
end Formalism.GradedWeylDivisibility
