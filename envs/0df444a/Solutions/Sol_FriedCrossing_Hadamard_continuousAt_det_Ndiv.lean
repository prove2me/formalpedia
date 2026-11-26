-- Prove2me | solution 1 for FriedCrossing.Hadamard.continuousAt_det_Ndiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:57:10.006813+00:00
-- url     : https://prove2.me/submissions/2a4c229a-9ebb-412d-935a-9a3e372f9af8

import Definitions.Def_B1s_fried_crossing_rate_9_07
import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
import Theorems.Thm_FriedCrossing_Hadamard_continuousAt_Ndiv_entry

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.Hadamard
namespace FriedCrossing.Hadamard
theorem _root_.solution (M M' : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (sStar : ℝ → ℝ)
    (h0 : ∀ θ, M θ 0 = sStar θ • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (hderiv : ∀ θ τ i j, HasDerivAt (fun t => M θ t i j) (M' θ τ i j) τ)
    (hM' : ∀ i j, ContinuousAt (fun p : ℝ × ℝ => M' p.1 p.2 i j) (0, 0)) :
    ContinuousAt (fun p : ℝ × ℝ => (Ndiv M M' sStar p.1 p.2).det) (0, 0) := by
  have h := continuousAt_Ndiv_entry M M' sStar h0 hderiv hM'
  simp only [Matrix.det_fin_two]
  exact ((h 0 0).mul (h 1 1)).sub ((h 0 1).mul (h 1 0))
end FriedCrossing.Hadamard
