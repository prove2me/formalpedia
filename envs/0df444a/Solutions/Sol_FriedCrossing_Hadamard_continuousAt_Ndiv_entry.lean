-- Prove2me | solution 1 for FriedCrossing.Hadamard.continuousAt_Ndiv_entry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:47:03.305085+00:00
-- url     : https://prove2.me/submissions/e1912618-6a0c-4294-8291-6b6239eb9530

import Definitions.Def_B1s_fried_crossing_rate_9_07
import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
import Theorems.Thm_FriedCrossing_Hadamard_Ndiv_zero
import Theorems.Thm_FriedCrossing_Hadamard_entry_slope_eq

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.Hadamard
namespace FriedCrossing.Hadamard
theorem _root_.solution (M M' : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (sStar : ℝ → ℝ)
    (h0 : ∀ θ, M θ 0 = sStar θ • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (hderiv : ∀ θ τ i j, HasDerivAt (fun t => M θ t i j) (M' θ τ i j) τ)
    (hM' : ∀ i j, ContinuousAt (fun p : ℝ × ℝ => M' p.1 p.2 i j) (0, 0)) (i j : Fin 2) :
    ContinuousAt (fun p : ℝ × ℝ => Ndiv M M' sStar p.1 p.2 i j) (0, 0) := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp (hM' i j) ε hε
  refine ⟨δ, hδ, fun p hp => ?_⟩
  obtain ⟨θ, τ⟩ := p
  have hp' : |θ| < δ ∧ |τ| < δ := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero, sub_zero, max_lt_iff] at hp
    exact hp
  -- the value at (0,0) is M' 0 0 i j
  have hN00 : Ndiv M M' sStar 0 0 i j = M' 0 0 i j := by rw [Ndiv_zero]
  rw [hN00]
  by_cases hτ : τ = 0
  · subst hτ
    rw [Ndiv_zero]
    have hd : dist ((θ, (0 : ℝ)) : ℝ × ℝ) (0, 0) < δ := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero, sub_zero]
      exact max_lt hp'.1 (by rw [abs_zero]; exact hδ)
    exact hball hd
  · -- difference quotient of the entry = derivative at some ξ with |ξ| < |τ|
    have hentry : Ndiv M M' sStar θ τ i j = (M θ τ i j - M θ 0 i j) / τ := by
      simp only [Ndiv, hτ, if_false, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, h0 θ]
      ring
    obtain ⟨ξ, hξ, hslope⟩ := entry_slope_eq (hderiv θ · i j) hτ
    rw [hentry, hslope]
    have hd : dist ((θ, ξ) : ℝ × ℝ) (0, 0) < δ := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero, sub_zero]
      exact max_lt hp'.1 (lt_trans hξ hp'.2)
    exact hball hd
end FriedCrossing.Hadamard
