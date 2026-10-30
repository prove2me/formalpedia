-- Prove2me | solution 1 for DerivativeChainPrivate.framed_power_chain_collision_limit
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T03:07:19.345932+00:00
-- url     : https://prove2.me/submissions/c0f8122d-c2ac-400f-ae5c-0789ac091d44

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
theorem solution (n k : ℕ) [NeZero n] (last : Fin n) (p : ℕ → Polynomial ℂ) (q : Polynomial ℂ)
    (hp : ∀ j, (p j).natDegree ≤ n) (hq : q.natDegree ≤ n)
    (hc : ∀ k, Tendsto (fun j => (p j).coeff k) atTop (𝓝 (q.coeff k)))
    (z : ℕ → Fin n → ℂ) (a b : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j i, ‖z j i‖ ≤ M)
    (hroot : ∀ j i, (Polynomial.derivative^[n-(i.val+1)] (p j)).eval (z j i) = 0)
    (η : ℂ) (hstart : ∀ j, z j 0 = η)
    (htail : ∀ j i, k ≤ i.val → z j i = z j last)
    (ha : ∀ j, ‖a j‖ = 1) (hb : ∀ j, ‖b j‖ = 1)
    (hab : ∀ j, (a j*starRingEnd ℂ (b j)).re = 0)
    (hmonoA : ∀ j, Monotone (fun i => (a j*z j i).re))
    (hmonoB : ∀ j, Monotone (fun i => (b j*z j i).re))
    (c : ℕ → ℝ) (C : ℝ) (hcLim : Tendsto c atTop (𝓝 C))
    (hcost : ∀ j, chainCost (z j) ≤ c j) :
    ∃ (w : Fin n → ℂ) (A B : ℂ),
      (∀ i, (Polynomial.derivative^[n-(i.val+1)] q).eval (w i) = 0) ∧
      w 0 = η ∧ (∀ i : Fin n, k ≤ i.val → w i = w last) ∧
      ‖A‖ = 1 ∧ ‖B‖ = 1 ∧ (A*starRingEnd ℂ B).re = 0 ∧
      Monotone (fun i => (A*w i).re) ∧ Monotone (fun i => (B*w i).re) ∧ chainCost w ≤ C := by
  let packed (j : ℕ) : ((Fin n → ℂ) × ℂ) × ℂ := ((z j,a j),b j)
  let S := max M 1
  have hS : 0 ≤ S := le_trans (by norm_num) (le_max_right M 1)
  have hmem (j : ℕ) : packed j ∈ Metric.closedBall 0 S := by
    rw [Metric.mem_closedBall,dist_zero_right]
    change max (max ‖z j‖ ‖a j‖) ‖b j‖ ≤ S
    have hzNorm : ‖z j‖ ≤ M := (pi_norm_le_iff_of_nonneg hM).mpr (hbound j)
    exact max_le (max_le (hzNorm.trans (le_max_left M 1))
      (by rw [ha]; exact le_max_right M 1)) (by rw [hb]; exact le_max_right M 1)
  obtain ⟨u,_,φ,hφ,hlim⟩ := (isCompact_closedBall (0 : ((Fin n → ℂ) × ℂ) × ℂ) S).isSeqCompact hmem
  let w := u.1.1
  let A := u.1.2
  let B := u.2
  have hφlim := hφ.tendsto_atTop
  have hzlim : Tendsto (fun j => z (φ j)) atTop (𝓝 w) := by
    have hc : Continuous (fun p : ((Fin n → ℂ) × ℂ) × ℂ => p.1.1) := continuous_fst.fst
    simpa only [Function.comp_def,packed,w] using hc.continuousAt.tendsto.comp hlim
  have hAlim : Tendsto (fun j => a (φ j)) atTop (𝓝 A) := by
    have hc : Continuous (fun p : ((Fin n → ℂ) × ℂ) × ℂ => p.1.2) := continuous_fst.snd
    simpa only [Function.comp_def,packed,A] using hc.continuousAt.tendsto.comp hlim
  have hBlim : Tendsto (fun j => b (φ j)) atTop (𝓝 B) := by
    have hc : Continuous (fun p : ((Fin n → ℂ) × ℂ) × ℂ => p.2) := continuous_snd
    simpa only [Function.comp_def,packed,B] using hc.continuousAt.tendsto.comp hlim
  have hcoord (i : Fin n) : Tendsto (fun j => z (φ j) i) atTop (𝓝 (w i)) :=
    (continuous_apply i).continuousAt.tendsto.comp hzlim
  refine ⟨w,A,B,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i
    have hrootlim := iterate_derivative_eval_tendsto (fun j => p (φ j)) q n
      (fun j => hp (φ j)) hq (fun k => (hc k).comp hφlim)
      (n-(i.val+1)) (fun j => z (φ j) i) (w i) (hcoord i)
    exact tendsto_nhds_unique hrootlim (by
      simpa only [hroot] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0)))
  · exact tendsto_nhds_unique (hcoord 0) (by
      simpa only [hstart] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => η) atTop (𝓝 η)))
  · intro i hi
    have h := hcoord i
    have heq : (fun j => z (φ j) i) = (fun j => z (φ j) last) :=
      funext (fun j => htail (φ j) i hi)
    rw [heq] at h
    exact tendsto_nhds_unique h (hcoord last)
  · exact tendsto_nhds_unique (continuous_norm.continuousAt.tendsto.comp hAlim) (by
      simpa only [Function.comp_def,ha] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)))
  · exact tendsto_nhds_unique (continuous_norm.continuousAt.tendsto.comp hBlim) (by
      simpa only [Function.comp_def,hb] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)))
  · have horthlim := Complex.continuous_re.continuousAt.tendsto.comp
      (hAlim.mul (Complex.continuous_conj.continuousAt.tendsto.comp hBlim))
    exact tendsto_nhds_unique horthlim (by
      simpa only [Function.comp_def,hab] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
  · intro i j hij
    exact le_of_tendsto_of_tendsto
      (Complex.continuous_re.continuousAt.tendsto.comp (hAlim.mul (hcoord i)))
      (Complex.continuous_re.continuousAt.tendsto.comp (hAlim.mul (hcoord j)))
      (Eventually.of_forall (fun s => hmonoA (φ s) hij))
  · intro i j hij
    exact le_of_tendsto_of_tendsto
      (Complex.continuous_re.continuousAt.tendsto.comp (hBlim.mul (hcoord i)))
      (Complex.continuous_re.continuousAt.tendsto.comp (hBlim.mul (hcoord j)))
      (Eventually.of_forall (fun s => hmonoB (φ s) hij))
  · have hcontinuous : Continuous (fun v : Fin n → ℂ => chainCost v) := by
      unfold chainCost
      fun_prop
    exact le_of_tendsto_of_tendsto (hcontinuous.continuousAt.tendsto.comp hzlim)
      (hcLim.comp hφlim) (Eventually.of_forall (fun j => hcost (φ j)))
