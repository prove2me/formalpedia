-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.fock_comp_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:55:19.250628+00:00
-- url     : https://prove2.me/submissions/e7a78694-e17e-477d-a8d7-2327caa9b95e

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_OrthogonalIsomorphismHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CommProjectionHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CompEqZeroOfNotDle
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_isWt_comp
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_fock_wt_ne
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_PW_fock_sum_right__325424ac65a7


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution {n : ℕ} (LL : Letters N) (j : ℕ) (e : Fin n ↪o Fin r) {μ : Fin n → ℤ}
    {x : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hx : (GAe p LL j e).IsWt μ x)
    (z : MvPolynomial (Fin N × Fin r) ℚ_[p]) : fock p x z = fock p x ((GAe p LL j e).comp μ z) := by
  classical
  obtain ⟨S, hS⟩ := (GAe p LL j e).dec z
  have hz := (GAe p LL j e).sum_comp z (insert μ S) (fun ν hν => hS ν (fun h => hν (Finset.mem_insert_of_mem h)))
  conv_lhs => rw [← hz]
  rw [fock_sum_right', Finset.sum_eq_single μ]
  · intro ν _ hν
    exact fock_wt_ne LL j e (Ne.symm hν) hx ((GAe p LL j e).isWt_comp ν z)
  · intro h
    exact absurd (Finset.mem_insert_self μ S) h
end Formalism.InvariantFactorPaths.PW
