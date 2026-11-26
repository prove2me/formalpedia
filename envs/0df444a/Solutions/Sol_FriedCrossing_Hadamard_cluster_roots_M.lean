-- Prove2me | solution 1 for FriedCrossing.Hadamard.cluster_roots_M
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:11:03.992683+00:00
-- url     : https://prove2.me/submissions/c5d541e5-3fab-4beb-b5b4-5d9a9295eabc

import Definitions.Def_B1s_fried_crossing_rate_9_07
import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
import Theorems.Thm_FriedCrossing_Hadamard_M_eq
import Theorems.Thm_FriedCrossing_Hadamard_trace_M
import Theorems.Thm_FriedCrossing_Hadamard_det_M
import Theorems.Thm_FriedCrossing_TwinRate_cluster_roots


set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.Hadamard
namespace FriedCrossing.Hadamard
theorem _root_.solution (M M' : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (sStar : ℝ → ℝ)
    (h0 : ∀ θ, M θ 0 = sStar θ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (θ τ : ℝ)
    (hD : 0 ≤ TwinRate.disc (Ndiv M M' sStar θ τ).trace (Ndiv M M' sStar θ τ).det) (z : ℝ) :
    z ^ 2 - (M θ τ).trace * z + (M θ τ).det = 0 ↔
      z = sStar θ + τ * TwinRate.wPlus (Ndiv M M' sStar θ τ).trace (Ndiv M M' sStar θ τ).det ∨
      z = sStar θ + τ * TwinRate.wMinus (Ndiv M M' sStar θ τ).trace (Ndiv M M' sStar θ τ).det := by
  rw [M_eq M M' sStar h0 θ τ, trace_M, det_M]
  exact TwinRate.cluster_roots hD z
end FriedCrossing.Hadamard
