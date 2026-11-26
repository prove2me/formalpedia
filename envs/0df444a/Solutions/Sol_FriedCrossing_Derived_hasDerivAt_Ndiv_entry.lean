-- Prove2me | solution 1 for FriedCrossing.Derived.hasDerivAt_Ndiv_entry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:05:14.584896+00:00
-- url     : https://prove2.me/submissions/0e6e329e-a97e-4999-a6c6-aae02e2db6c2

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Theorems.Thm_FriedCrossing_HQuot_hasDerivAt_hq
import Theorems.Thm_P2M_FriedCrossing_Derived_contDiff_M___151935ad3aa9
import Theorems.Thm_FriedCrossing_Derived_hasDerivAt_M
import Theorems.Thm_P2M_FriedCrossing_Derived_hasDerivAt_M__92e08b1bff5c
import Theorems.Thm_FriedCrossing_Derived_Ndiv_eq_hq

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
    (hsemi : ∀ θ, M θ 0 = sStar θ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (θ τ : ℝ) (i j : Fin 2) :
    HasDerivAt (fun τ => Ndiv M (Mτ M) sStar θ τ i j) (Nτ M θ τ i j) τ := by
  have heq : (fun τ => Ndiv M (Mτ M) sStar θ τ i j) =
      hq (fun t => M θ t i j) (fun t => Mτ M θ t i j) := funext fun τ => Ndiv_eq_hq hsemi θ τ i j
  have hc : Continuous fun t => Mττ M θ t i j :=
    (contDiff_Mττ h i j).continuous.comp (continuous_const.prodMk continuous_id)
  rw [heq]
  exact hasDerivAt_hq (fun t => hasDerivAt_M h θ t i j) (fun t => hasDerivAt_Mτ h θ t i j)
    hc.continuousAt τ
end FriedCrossing.Derived
