-- Prove2me | solution 1 for Formalism.QuantumDeterminants.formal_degree_factorial_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:43:11.529882+00:00
-- url     : https://prove2.me/submissions/372c2491-2707-47e0-9cab-271e6434000a

import Definitions.Def_Formalism_FormalDegreeBessel_HolDimLowK
import Definitions.Def_Formalism_FormalDegreeBessel_FinalDS
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_HolomorphicLowKDimensionHolds
import Theorems.Thm_Formalism_QuantumDeterminants_prod_lt_sub_eq_factorial

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
theorem _root_.solution : FdegFactorial := by
  intro n
  have hswap : (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b),
      (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) =
      ∏ b : Fin n, ∏ a ∈ univ.filter (fun a : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
    simp_rw [Finset.prod_filter]
    exact Finset.prod_comm
  rw [hswap]
  simp_rw [prod_lt_sub_eq_factorial]
  exact Fin.prod_univ_eq_prod_range (fun i => ((i.factorial : ℕ) : ℝ)) n
end Formalism.QuantumDeterminants
