-- Prove2me | solution 2 for Formalism.QuantumDeterminants.prod_range_sub_cast_eq_factorial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:12:42.243937+00:00
-- url     : https://prove2.me/submissions/82777778-a28c-4121-802d-bb843673030e

import Definitions.Def_Formalism_FormalDegreeBessel_HolDimLowK
import Definitions.Def_Formalism_FormalDegreeBessel_FinalDS
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_HolomorphicLowKDimensionHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.REAL
namespace Formalism.QuantumDeterminants
theorem _root_.solution (b : ℕ) :
    ∏ j ∈ range b, ((b : ℝ) - (j : ℝ)) = (b.factorial : ℝ) := by
  have h := Finset.prod_range_reflect (fun j : ℕ => ((b : ℝ) - (j : ℝ))) b
  rw [← h, ← Finset.prod_range_add_one_eq_factorial]
  push_cast
  refine Finset.prod_congr rfl fun j hj => ?_
  have hj' : j < b := Finset.mem_range.mp hj
  have : ((b - 1 - j : ℕ) : ℝ) = (b : ℝ) - 1 - (j : ℝ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
  rw [this]; ring
end Formalism.QuantumDeterminants
