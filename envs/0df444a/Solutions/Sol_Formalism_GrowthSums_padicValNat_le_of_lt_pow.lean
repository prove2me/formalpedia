-- Prove2me | solution 1 for Formalism.GrowthSums.padicValNat_le_of_lt_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:06.054799+00:00
-- url     : https://prove2.me/submissions/9c4bfddd-57d1-4bce-888a-b7969150cdc1

import Definitions.Def_Formalism_GrowthSums_StatementA
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_Harmonic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Finset
open Formalism Formalism.GrowthSums
namespace Formalism.GrowthSums
theorem _root_.solution {p t y : ℕ} [hp : Fact p.Prime] (hy : 1 ≤ y)
    (hyP : y < p ^ (t + 1)) : padicValNat p y ≤ t := by
  by_contra h
  push_neg at h
  have hdvd : p ^ (t + 1) ∣ y :=
    (pow_dvd_pow p (Nat.succ_le_of_lt h)).trans pow_padicValNat_dvd
  exact absurd (Nat.le_of_dvd (by omega) hdvd) (not_le.2 hyP)
end Formalism.GrowthSums
