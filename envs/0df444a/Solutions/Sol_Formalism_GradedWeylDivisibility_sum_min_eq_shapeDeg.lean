-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.sum_min_eq_shapeDeg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:20.248134+00:00
-- url     : https://prove2.me/submissions/da7868e4-d872-4b21-8e57-2cc579564c31

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetdomLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (k : ℕ) :
    ∑ k' : Fin K, min k (sz k') = ∑ t : Fin n with t.val < k, shapeDeg sz t := by
  classical
  unfold shapeDeg
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k' _
  rw [Finset.sum_boole, Finset.filter_filter]
  have e : #{t : Fin n | t.val < k ∧ t.val < sz k'} = #{t : Fin n | t.val < min k (sz k')} := by
    congr 1; ext t; simp [lt_min_iff]
  rw [Nat.cast_id, e, Fin.card_filter_val_lt]
  have := hsz k'
  omega
end Formalism.GradedWeylDivisibility
