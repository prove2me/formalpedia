-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.INST.spr_le_bidet
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:09:47.448235+00:00
-- url     : https://prove2.me/submissions/68ac58e4-bb18-41b2-afa6-e2567af75e5c

import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SpreadSquare
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDrowLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_Spread
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_spr_rowDeg_bidet
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_spr_one_le_count

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.INST
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.INST
theorem _root_.solution (R : Type*) [CommRing R] {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin n) (hI : ∀ k, Function.Injective (I k)) (lo : ℕ)
    (hlo : ∀ t : Fin n, lo ≤ shapeDeg sz t)
    (m : Fin n × Fin n →₀ ℕ) (hm : m ∈ (bideterminant R sz hsz I).support) (a : Fin n) : lo ≤ rowDeg m a := by
  classical
  rw [spr_rowDeg_bidet R sz hsz I m hm a]
  have hn : n - 1 < n := by have := a.isLt; omega
  refine (hlo ⟨n - 1, hn⟩).trans ?_
  unfold shapeDeg
  rw [Finset.card_filter]
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases hk : n - 1 < sz k
  · rw [if_pos hk]
    exact spr_one_le_count (I k) (hI k) (by have := hsz k; omega) a
  · rw [if_neg hk]
    exact Nat.zero_le _
end Formalism.InvariantFactorPaths.INST
