-- Prove2me | solution 1 for FriedCrossing.Derived.hasDerivAt_det_Ndiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:06:15.342459+00:00
-- url     : https://prove2.me/submissions/c5f21d68-112d-4b48-82c7-ff0f3dd20af7

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
    HasDerivAt (fun τ => (Ndiv M (Mτ M) sStar θ τ).det) (bτ M sStar θ τ) τ := by
  simp only [Matrix.det_fin_two, bτ]
  exact ((hasDerivAt_Ndiv_entry h hsemi θ τ 0 0).mul (hasDerivAt_Ndiv_entry h hsemi θ τ 1 1)).sub
    ((hasDerivAt_Ndiv_entry h hsemi θ τ 0 1).mul (hasDerivAt_Ndiv_entry h hsemi θ τ 1 0))
end FriedCrossing.Derived
