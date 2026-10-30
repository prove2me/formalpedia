-- Prove2me | solution 1 for DerivativeChainContinuation.coordinate_chain_collision_limit_with_fixed_start
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T02:40:45.197654+00:00
-- url     : https://prove2.me/submissions/13d4673e-2b21-4e6c-ba73-391f61c2f089

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


open Polynomial DerivativeChainPrivate
set_option autoImplicit false



set_option autoImplicit false

namespace DerivativeChainPrivate









end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial









end DerivativeChainPrivate



set_option autoImplicit false
open scoped BigOperators

namespace DerivativeChainPrivate













end DerivativeChainPrivate



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



set_option autoImplicit false
open scoped BigOperators
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial







end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate











end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate







end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial









end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial







end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
open Filter Topology
namespace DerivativeChainPrivate
open Polynomial











end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate









end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



open DerivativeChainPrivate in
theorem solution (n k : ℕ) [NeZero n] (last : Fin n)
    (p : ℕ → Polynomial ℂ) (q : Polynomial ℂ)
    (hp : ∀ j, (p j).natDegree ≤ n) (hq : q.natDegree ≤ n)
    (hc : ∀ k, Tendsto (fun j => (p j).coeff k) atTop (𝓝 (q.coeff k)))
    (z : ℕ → Fin n → ℂ) (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ j i, ‖z j i‖ ≤ M)
    (hroot : ∀ j i, (Polynomial.derivative^[n-(i.val+1)] (p j)).eval (z j i)=0)
    (η : ℂ) (hstart : ∀ j, z j 0=η)
    (htail : ∀ j i, k ≤ i.val → z j i=z j last)
    (hmonoR : ∀ j, Monotone (fun i => (z j i).re))
    (hmonoI : ∀ j, Monotone (fun i => (z j i).im)) :
    ∃ w : Fin n → ℂ,
      (∀ i, (Polynomial.derivative^[n-(i.val+1)] q).eval (w i)=0) ∧
      w 0=η ∧ (∀ i : Fin n, k ≤ i.val → w i=w last) ∧
      Monotone (fun i => (w i).re) ∧ Monotone (fun i => (w i).im) := by
  have hmem (j : ℕ) : z j ∈ Metric.closedBall (0:Fin n → ℂ) M := by
    rw [Metric.mem_closedBall,dist_zero_right]
    exact (pi_norm_le_iff_of_nonneg hM).mpr (hbound j)
  obtain ⟨w,_,φ,hφ,hlim⟩ := (isCompact_closedBall (0:Fin n → ℂ) M).isSeqCompact hmem
  have hφlim := hφ.tendsto_atTop
  have hcoord (i : Fin n) : Tendsto (fun j => z (φ j) i) atTop (𝓝 (w i)) :=
    (continuous_apply i).continuousAt.tendsto.comp hlim
  refine ⟨w,?_,?_,?_,?_,?_⟩
  · intro i
    have hh := iterate_derivative_eval_tendsto (fun j => p (φ j)) q n
      (fun j => hp (φ j)) hq (fun k => (hc k).comp hφlim)
      (n-(i.val+1)) (fun j => z (φ j) i) (w i) (hcoord i)
    exact tendsto_nhds_unique hh (by simpa only [hroot] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℂ)) atTop (𝓝 0)))
  · exact tendsto_nhds_unique (hcoord 0) (by simpa only [hstart] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => η) atTop (𝓝 η)))
  · intro i hi
    have hh := hcoord i
    have he : (fun j => z (φ j) i) = (fun j => z (φ j) last) := funext (fun j => htail (φ j) i hi)
    rw [he] at hh
    exact tendsto_nhds_unique hh (hcoord last)
  · intro i j hij
    exact le_of_tendsto_of_tendsto
      (Complex.continuous_re.continuousAt.tendsto.comp (hcoord i))
      (Complex.continuous_re.continuousAt.tendsto.comp (hcoord j))
      (Eventually.of_forall (fun t => hmonoR (φ t) hij))
  · intro i j hij
    exact le_of_tendsto_of_tendsto
      (Complex.continuous_im.continuousAt.tendsto.comp (hcoord i))
      (Complex.continuous_im.continuousAt.tendsto.comp (hcoord j))
      (Eventually.of_forall (fun t => hmonoI (φ t) hij))
