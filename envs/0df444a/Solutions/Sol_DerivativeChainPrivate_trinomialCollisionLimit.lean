-- Prove2me | solution 1 for DerivativeChainPrivate.trinomialCollisionLimit
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-18T07:42:53.775997+00:00
-- url     : https://prove2.me/submissions/ca3d2938-da1d-4bdb-900e-2520a0ee0316

import Definitions.Def_DerivativeChainPrivate_foundations
open Filter Topology
open scoped BigOperators
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
open scoped BigOperators
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
open Set
namespace DerivativeChainPrivate























end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate











end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
namespace DerivativeChainPrivate







end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
namespace DerivativeChainPrivate













end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
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

theorem complete_chain_collision_limit {n N : ℕ} (p : ℕ → Polynomial ℂ)
    (q : Polynomial ℂ) (hp : ∀ j, (p j).natDegree ≤ N) (hq : q.natDegree ≤ N)
    (hc : ∀ k, Tendsto (fun j => (p j).coeff k) atTop (𝓝 (q.coeff k)))
    (z : ℕ → Fin n → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hzbound : ∀ j i, ‖z j i‖ ≤ R)
    (hzroot : ∀ j i, (Polynomial.derivative^[n - (i.val + 1)] (p j)).eval (z j i) = 0)
    (c : ℕ → ℝ) (C : ℝ) (hcLim : Tendsto c atTop (𝓝 C))
    (hcost : ∀ j, chainCost (z j) ≤ c j) :
    ∃ w : Fin n → ℂ,
      (∀ i, (Polynomial.derivative^[n - (i.val + 1)] q).eval (w i) = 0) ∧ chainCost w ≤ C := by
  have hmem (j : ℕ) : z j ∈ Metric.closedBall (0 : Fin n → ℂ) R := by
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hR]
    exact hzbound j
  obtain ⟨w, _, phi, hphi, hlim⟩ :=
    (isCompact_closedBall (0 : Fin n → ℂ) R).isSeqCompact hmem
  have hphilim : Tendsto phi atTop atTop := hphi.tendsto_atTop
  refine ⟨w, ?_, ?_⟩
  · intro i
    have hcoord : Tendsto (fun j => z (phi j) i) atTop (𝓝 (w i)) :=
      (continuous_apply i).continuousAt.tendsto.comp hlim
    have hrootlim := iterate_derivative_eval_tendsto (fun j => p (phi j)) q N
      (fun j => hp (phi j)) hq (fun k => (hc k).comp hphilim)
      (n - (i.val + 1)) (fun j => z (phi j) i) (w i) hcoord
    have hzero : Tendsto
        (fun j => (Polynomial.derivative^[n - (i.val + 1)] (p (phi j))).eval (z (phi j) i))
        atTop (𝓝 (0 : ℂ)) := by
      simpa only [hzroot] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
    exact tendsto_nhds_unique hrootlim hzero
  · have hcontinuous : Continuous (fun v : Fin n → ℂ => chainCost v) := by
      unfold chainCost
      fun_prop
    exact le_of_tendsto_of_tendsto (hcontinuous.continuousAt.tendsto.comp hlim)
      (hcLim.comp hphilim) (Eventually.of_forall (fun j => hcost (phi j)))

end DerivativeChainPrivate



set_option autoImplicit false
open Filter Topology
namespace DerivativeChainPrivate



end DerivativeChainPrivate

open DerivativeChainPrivate in
theorem solution {n : ℕ} (_hn : 0 < n)
    (p : ℕ → Polynomial ℂ) (q : Polynomial ℂ)
    (hp : ∀ j, (p j).natDegree = n) (hq : q.natDegree = n)
    (hc : ∀ k, Tendsto (fun j => (p j).coeff k) atTop (𝓝 (q.coeff k)))
    (z : ℕ → Fin n → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hzbound : ∀ j i, ‖z j i‖ ≤ R)
    (hzroot : ∀ j i, (Polynomial.derivative^[n - (i.val + 1)] (p j)).eval (z j i) = 0)
    (c : ℕ → ℝ) (C : ℝ) (hcLim : Tendsto c atTop (𝓝 C))
    (hcost : ∀ j, chainCost (z j) ≤ c j) :
    ∃ w : Fin n → ℂ,
      (∀ i, (Polynomial.derivative^[n - (i.val + 1)] q).eval (w i) = 0) ∧ chainCost w ≤ C := by
  exact complete_chain_collision_limit (N := n) p q (fun j => (hp j).le) hq.le
    hc z R hR hzbound hzroot c C hcLim hcost
