-- Prove2me | solution 1 for FriedCrossing.Derived.Ndiv_eq_hq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:01:26.242804+00:00
-- url     : https://prove2.me/submissions/b8bed7f2-4250-4482-a734-e5a7cd322adf

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Derived
open Regularity HQuot Hadamard ClusterMatrix Ledger
variable {M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ} {A : ℝ → ℝ → Matrix (Fin 4) (Fin 4) ℝ}
  {sStar : ℝ → ℝ}
namespace FriedCrossing.Derived
theorem _root_.solution (hsemi : ∀ θ, M θ 0 = sStar θ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (θ τ : ℝ)
    (i j : Fin 2) :
    Ndiv M (Mτ M) sStar θ τ i j = hq (fun t => M θ t i j) (fun t => Mτ M θ t i j) τ := by
  unfold Ndiv hq
  split_ifs with hτ
  · rfl
  · simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, hsemi θ]
    ring
end FriedCrossing.Derived
