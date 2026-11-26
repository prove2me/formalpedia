-- Prove2me | solution 1 for FriedCrossing.Derived.hasDerivAt_trace_Ndiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:06:10.882858+00:00
-- url     : https://prove2.me/submissions/c4c601af-0d78-4cb7-9a7b-0d57e5fba23b

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Theorems.Thm_FriedCrossing_Derived_hasDerivAt_Ndiv_entry

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Derived
open Regularity HQuot Hadamard ClusterMatrix Ledger
variable {M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ} {A : ℝ → ℝ → Matrix (Fin 4) (Fin 4) ℝ}
  {sStar : ℝ → ℝ}
namespace FriedCrossing.Derived
theorem _root_.solution (h : ClusterC3 M A)
    (hsemi : ∀ θ, M θ 0 = sStar θ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (θ τ : ℝ) :
    HasDerivAt (fun τ => (Ndiv M (Mτ M) sStar θ τ).trace) (aτ M θ τ) τ := by
  simp only [Matrix.trace_fin_two, aτ]
  exact (hasDerivAt_Ndiv_entry h hsemi θ τ 0 0).add (hasDerivAt_Ndiv_entry h hsemi θ τ 1 1)
end FriedCrossing.Derived
