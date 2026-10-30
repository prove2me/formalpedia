-- Prove2me | solution 1 for DerivativeChainPrivate.coordinate_chain_collision_limit
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:18:20.089995+00:00
-- url     : https://prove2.me/submissions/6d8d55eb-2e4f-40a5-86d1-20b26d4f6db8

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
namespace DerivativeChainPrivate
end DerivativeChainPrivate
open DerivativeChainPrivate Filter Topology Polynomial
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
open scoped BigOperators
namespace DerivativeChainPrivate

theorem polynomial_eval_tendsto_of_coeff (p : ℕ → Polynomial ℂ) (q : Polynomial ℂ)
    (N : ℕ) (hp : ∀ j, (p j).natDegree ≤ N) (hq : q.natDegree ≤ N)
    (hc : ∀ k, Tendsto (fun j => (p j).coeff k) atTop (𝓝 (q.coeff k)))
    (z : ℕ → ℂ) (w : ℂ) (hz : Tendsto z atTop (𝓝 w)) :
    Tendsto (fun j => (p j).eval (z j)) atTop (𝓝 (q.eval w)) := by
  have heval (j : ℕ) : (p j).eval (z j) =
      ∑ k ∈ Finset.range (N + 1), (p j).coeff k * (z j) ^ k :=
    Polynomial.eval_eq_sum_range' (by have := hp j; omega) _
  have hqeval : q.eval w = ∑ k ∈ Finset.range (N + 1), q.coeff k * w ^ k :=
    Polynomial.eval_eq_sum_range' (by omega) _
  rw [hqeval]
  have hs : Tendsto (fun j => ∑ k ∈ Finset.range (N + 1), (p j).coeff k * (z j) ^ k)
      atTop (𝓝 (∑ k ∈ Finset.range (N + 1), q.coeff k * w ^ k)) :=
    tendsto_finsetSum _ (fun k _ => (hc k).mul (hz.pow k))
  exact hs.congr' (Eventually.of_forall (fun j => (heval j).symm))

theorem iterate_derivative_eval_tendsto (p : ℕ → Polynomial ℂ) (q : Polynomial ℂ)
    (N : ℕ) (hp : ∀ j, (p j).natDegree ≤ N) (hq : q.natDegree ≤ N)
    (hc : ∀ k, Tendsto (fun j => (p j).coeff k) atTop (𝓝 (q.coeff k)))
    (k : ℕ) (z : ℕ → ℂ) (w : ℂ) (hz : Tendsto z atTop (𝓝 w)) :
    Tendsto (fun j => (Polynomial.derivative^[k] (p j)).eval (z j))
      atTop (𝓝 ((Polynomial.derivative^[k] q).eval w)) := by
  apply polynomial_eval_tendsto_of_coeff _ _ N
    (fun j => (Polynomial.natDegree_iterate_derivative (p j) k).trans
      ((Nat.sub_le _ _).trans (hp j)))
    ((Polynomial.natDegree_iterate_derivative q k).trans ((Nat.sub_le _ _).trans hq)) _ z w hz
  intro m
  simp only [Polynomial.coeff_iterate_derivative, nsmul_eq_mul]
  exact tendsto_const_nhds.mul (hc (m + k))



end DerivativeChainPrivate

open DerivativeChainPrivate in
theorem solution {n N : ℕ}
    (p : ℕ → Polynomial ℂ) (q : Polynomial ℂ)
    (hp : ∀ j, (p j).natDegree ≤ N) (hq : q.natDegree ≤ N)
    (hc : ∀ k, Tendsto (fun j => (p j).coeff k) atTop (𝓝 (q.coeff k)))
    (z : ℕ → Fin n → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hzbound : ∀ j i, ‖z j i‖ ≤ R)
    (hzroot : ∀ j i, (Polynomial.derivative^[n - (i.val + 1)] (p j)).eval (z j i) = 0)
    (c : ℕ → ℝ) (C : ℝ) (hcLim : Tendsto c atTop (𝓝 C))
    (hcost : ∀ j, chainCost (z j) ≤ c j)
    (hre : ∀ j, Monotone (fun i => (z j i).re))
    (him : ∀ j, Monotone (fun i => (z j i).im))
    (k : ℕ) (last : Fin n) (htail : ∀ j i, k ≤ i.val → z j i = z j last) :
    ∃ w : Fin n → ℂ,
      (∀ i, (Polynomial.derivative^[n - (i.val + 1)] q).eval (w i) = 0) ∧
      chainCost w ≤ C ∧ Monotone (fun i => (w i).re) ∧
      Monotone (fun i => (w i).im) ∧ (∀ i, k ≤ i.val → w i = w last) := by
  have hmem (j : ℕ) : z j ∈ Metric.closedBall (0 : Fin n → ℂ) R := by
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hR]
    exact hzbound j
  obtain ⟨w, _, φ, hφ, hlim⟩ :=
    (isCompact_closedBall (0 : Fin n → ℂ) R).isSeqCompact hmem
  have hφlim := hφ.tendsto_atTop
  have hcoord (i : Fin n) : Tendsto (fun j => z (φ j) i) atTop (𝓝 (w i)) :=
    (continuous_apply i).continuousAt.tendsto.comp hlim
  refine ⟨w, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have hrootlim := iterate_derivative_eval_tendsto (fun j => p (φ j)) q N
      (fun j => hp (φ j)) hq (fun d => (hc d).comp hφlim)
      (n - (i.val + 1)) (fun j => z (φ j) i) (w i) (hcoord i)
    have hzero : Tendsto
        (fun j => (Polynomial.derivative^[n - (i.val + 1)] (p (φ j))).eval (z (φ j) i))
        atTop (𝓝 (0 : ℂ)) := by
      simpa only [hzroot] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
    exact tendsto_nhds_unique hrootlim hzero
  · have hcontinuous : Continuous (fun v : Fin n → ℂ => chainCost v) := by
      unfold chainCost
      fun_prop
    exact le_of_tendsto_of_tendsto (hcontinuous.continuousAt.tendsto.comp hlim)
      (hcLim.comp hφlim) (Eventually.of_forall (fun j => hcost (φ j)))
  · intro i j hij
    exact le_of_tendsto_of_tendsto
      (Complex.continuous_re.continuousAt.tendsto.comp (hcoord i))
      (Complex.continuous_re.continuousAt.tendsto.comp (hcoord j))
      (Eventually.of_forall (fun s => hre (φ s) hij))
  · intro i j hij
    exact le_of_tendsto_of_tendsto
      (Complex.continuous_im.continuousAt.tendsto.comp (hcoord i))
      (Complex.continuous_im.continuousAt.tendsto.comp (hcoord j))
      (Eventually.of_forall (fun s => him (φ s) hij))
  · intro i hi
    have hsame : (fun j => z (φ j) i) = (fun j => z (φ j) last) :=
      funext (fun j => htail (φ j) i hi)
    have hci := hcoord i
    rw [hsame] at hci
    exact tendsto_nhds_unique hci (hcoord last)
