-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.wt_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:47:21.177875+00:00
-- url     : https://prove2.me/submissions/59ac45e1-3e5d-4d91-8579-52a531ca3a22

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_rw_rw

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
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
theorem _root_.solution {n N : ℕ} (v : Bool) {m h : Fin n} (hmh : if v then m < h else h < m) :
    wt n N v (N, m) < wt n N v (N, h) := by
  have hba : rw_ v h < rw_ v m := by
    cases v
    · simpa [rw_] using hmh
    · simpa [rw_, Fin.rev_lt_rev] using hmh
  have key : ∀ a j : Fin n, (wt n N v (N, a) : Fin n → ℕ) j = if j = rw_ v a then 1 else 0 := by
    intro a j
    show (Finsupp.single (N, a) 1 : ℕ × Fin n →₀ ℕ) (N, rw_ v j) = _
    rw [Finsupp.single_apply]
    by_cases hj : j = rw_ v a
    · rw [if_pos hj, if_pos]
      rw [hj, rw_rw]
    · rw [if_neg hj, if_neg]
      intro he
      apply hj
      rw [(Prod.mk.inj he).2, rw_rw]
  refine ⟨rw_ v h, fun j hj => ?_, ?_⟩
  · rw [key, key, if_neg, if_neg]
    · exact ne_of_lt hj
    · exact ne_of_lt (lt_trans hj hba)
  · beta_reduce
    rw [key, key, if_neg (ne_of_lt hba), if_pos rfl]
    exact Nat.zero_lt_one
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
