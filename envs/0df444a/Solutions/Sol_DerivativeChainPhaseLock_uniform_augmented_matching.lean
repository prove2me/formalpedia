-- Prove2me | solution 1 for DerivativeChainPhaseLock.uniform_augmented_matching
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T06:18:53.60706+00:00
-- url     : https://prove2.me/submissions/53996d9a-3c9a-4dfd-91be-2cfa1d581660

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CollinearTransport
import Definitions.Def_DerivativeChainContinuation_UniformRootTower
import Theorems.Thm_DerivativeChainContinuation_finite_weighted_variance
import Theorems.Thm_DerivativeChainPhaseLock_birkhoff_cost_selection
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainFiniteHistory
end DerivativeChainFiniteHistory
namespace DerivativeChainPhaseLock
end DerivativeChainPhaseLock
namespace DerivativeChainPrefixLaws
end DerivativeChainPrefixLaws
namespace DerivativeChainPrivate
end DerivativeChainPrivate


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
open Polynomial Matrix DerivativeChainContinuation
namespace DerivativeChainPhaseLock
noncomputable section

theorem doubly_stochastic_variance_cost {N : ℕ} (a z : Fin N → ℂ) (u : ℂ)
    (S : Matrix (Fin N) (Fin N) ℝ) (hS : S ∈ doublyStochastic ℝ (Fin N))
    (hm : ∀ i,∑ j,(S i j:ℂ)*a j=z i) :
    (∑ i,∑ j,S i j*‖a j-z i‖^2)=
      (∑ j,‖a j-u‖^2)-(∑ i,‖z i-u‖^2) := by
  obtain ⟨hn,hr,hc⟩ := mem_doublyStochastic_iff_sum.mp hS
  have hv (i : Fin N) := finite_weighted_variance (S i) a (z i) u (hr i) (hm i)
  have hsum := congrArg (fun f : Fin N → ℝ => ∑ i,f i) (funext hv)
  have hleft : (∑ i,∑ j,S i j*‖a j-u‖^2)=∑ j,‖a j-u‖^2 := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul,hc,one_mul]
  simp only [Finset.sum_add_distrib] at hsum
  rw [hleft] at hsum
  linarith





end
end DerivativeChainPhaseLock



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
open Polynomial Matrix DerivativeChainContinuation
open DerivativeChainPhaseLock




theorem solution (r : _root_.DerivativeChainContinuation.ComplexRootRows) (k : ℕ)
    (hstep : _root_.DerivativeChainContinuation.UniformPolynomialStep r k) :
    ∃ σ : Equiv.Perm (Fin (k+2)),
      (∑ i,‖r (k+1) (σ i)-(Fin.snoc (r k) (_root_.DerivativeChainContinuation.complexCentroid (r (k+1))) : Fin (k+2) → ℂ) i‖^2) ≤
      (∑ j,‖r (k+1) j-_root_.DerivativeChainContinuation.complexCentroid (r (k+1))‖^2)-
      (∑ i,‖r k i-_root_.DerivativeChainContinuation.complexCentroid (r (k+1))‖^2) := by
  classical
  obtain ⟨hder,K,hK,hKs,hKm,hKcol⟩ := hstep
  let u := _root_.DerivativeChainContinuation.complexCentroid (r (k+1))
  let z : Fin (k+2) → ℂ := Fin.snoc (r k) u
  let S : Matrix (Fin (k+2)) (Fin (k+2)) ℝ :=
    Fin.lastCases (fun _ => (k+2:ℝ)⁻¹) K
  have hS0 (j : Fin (k+1)) (i : Fin (k+2)) : S j.castSucc i=K j i := by simp [S]
  have hS1 (i : Fin (k+2)) : S (Fin.last (k+1)) i=(k+2:ℝ)⁻¹ := by simp [S]
  have hcol (i : Fin (k+2)) : (∑ j,K j i)=(k+1:ℝ)*(k+2:ℝ)⁻¹ := by
    have h := hKcol i
    rw [← Finset.mul_sum] at h
    have hn : (k+1:ℝ) ≠ 0 := by positivity
    calc
      _ = (k+1:ℝ)*((k+1:ℝ)⁻¹*(∑ j,K j i)) := by rw [← mul_assoc,mul_inv_cancel₀ hn,one_mul]
      _ = _ := by rw [h]
  have hS : S ∈ doublyStochastic ℝ (Fin (k+2)) := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨?_,?_,?_⟩
    · intro j i
      refine Fin.lastCases ?_ (fun j => ?_) j
      · rw [hS1]; positivity
      · rw [hS0]; exact hK j i
    · intro j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simp only [hS1,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        push_cast
        exact mul_inv_cancel₀ (by positivity : (k+2:ℝ) ≠ 0)
      · simp only [hS0,hKs]
    · intro i
      rw [Fin.sum_univ_castSucc]
      simp only [hS0,hS1,hcol]
      have hn : (k+2:ℝ) ≠ 0 := by positivity
      field_simp
      ring
  have hm : ∀ i,∑ j,(S i j:ℂ)*r (k+1) j=z i := by
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [z,Fin.snoc_last,hS1,← Finset.mul_sum]
      dsimp [u,_root_.DerivativeChainContinuation.complexCentroid]
      push_cast
      ring
    · simpa only [z,Fin.snoc_castSucc,hS0] using hKm i
  have hv := _root_.DerivativeChainPhaseLock.doubly_stochastic_variance_cost (r (k+1)) z u S hS hm
  obtain ⟨σ,hσ⟩ := _root_.DerivativeChainPhaseLock.birkhoff_cost_selection S hS (fun i j => ‖r (k+1) j-z i‖^2)
  refine ⟨σ,?_⟩
  rw [hv] at hσ
  have hzsum : (∑ i,‖z i-u‖^2)=∑ i,‖r k i-u‖^2 := by
    rw [Fin.sum_univ_castSucc]
    simp [z]
  rw [hzsum] at hσ
  exact hσ
