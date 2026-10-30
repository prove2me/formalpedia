-- Prove2me | solution 1 for DerivativeChainClusterAnchor.uniform_complete_history_law
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T00:26:42.31306+00:00
-- url     : https://prove2.me/submissions/d35327b3-f848-4661-9773-80d1a8658781

import Mathlib
import Definitions.Def_DerivativeChainContinuation_FiniteRootHistories
import Definitions.Def_DerivativeChainContinuation_UniformRootTower
import Theorems.Thm_DerivativeChainContinuation_finite_weighted_variance
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainClusterAnchor
end DerivativeChainClusterAnchor
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainExtremal
end DerivativeChainExtremal
namespace DerivativeChainPrefixLaws
end DerivativeChainPrefixLaws
namespace DerivativeChainPrivate
end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open DerivativeChainContinuation
open DerivativeChainClusterAnchor


theorem solution (r : _root_.DerivativeChainContinuation.ComplexRootRows) (h : ℕ)
    (hstep : ∀ k<h, _root_.DerivativeChainContinuation.UniformPolynomialStep r k) :
    ∃ (κ : Type) (inst : Fintype κ), letI := inst;
      ∃ (w : κ → ℝ) (z : κ → ℕ → ℂ) (last : κ → Fin (h+1)),
        (∀ i, 0 ≤ w i) ∧ (∑ i, w i=1) ∧
        (∀ i, z i h=r h (last i)) ∧
        (∀ i k, k ≤ h → ∃ j : Fin (k+1), z i k=r k j) ∧
        (∀ f : Fin (h+1) → ℝ, (∑ i, w i*f (last i))=∑ j, (h+1:ℝ)⁻¹*f j) ∧
        (∑ i, (w i:ℂ)*z i h)=r 0 0 ∧
        (∑ i, w i*_root_.DerivativeChainContinuation.historyEnergy h (z i))=(∑ i, w i*‖z i h-r 0 0‖^2) := by
  classical
  induction h with
  | zero =>
    refine ⟨Fin 1,inferInstance,(fun _ => 1),(fun _ _ => r 0 0),id,?_,?_,?_,?_,?_,?_,?_⟩
    · intro i; norm_num
    · simp
    · intro i; rw [show i=0 from Fin.eq_zero i]; rfl
    · intro i k hk
      have he : k=0 := by omega
      subst k
      exact ⟨0,rfl⟩
    · intro f; simp
    · simp
    · simp [_root_.DerivativeChainContinuation.historyEnergy]
  | succ h ih =>
    obtain ⟨κ,inst,hdata⟩ := ih (fun k hk => hstep k (by omega))
    letI : Fintype κ := inst
    obtain ⟨w,z,last,hw0,hws,hend,hroots,hmarg,hmean,henergy⟩ := hdata
    obtain ⟨_,K,hK,hKs,hKm,hKcol⟩ := hstep h (by omega)
    let W : κ × Fin (h+2) → ℝ := fun ij => w ij.1*K (last ij.1) ij.2
    let Z : κ × Fin (h+2) → ℕ → ℂ := fun ij k => if k ≤ h then z ij.1 k else r (h+1) ij.2
    have hZEnd (i : κ) (j : Fin (h+2)) : Z (i,j) (h+1)=r (h+1) j := by simp [Z]
    have hZE (i : κ) (j : Fin (h+2)) : _root_.DerivativeChainContinuation.historyEnergy (h+1) (Z (i,j)) =
        _root_.DerivativeChainContinuation.historyEnergy h (z i)+‖r (h+1) j-z i h‖^2 := by
      rw [_root_.DerivativeChainContinuation.historyEnergy,Finset.sum_range_succ]
      congr 1
      · apply Finset.sum_congr rfl
        intro k hk
        simp [Z,show k ≤ h by have := Finset.mem_range.mp hk; omega,
          show k+1 ≤ h by have := Finset.mem_range.mp hk; omega]
      · simp [Z]
    have hWs : ∑ ij, W ij=1 := by
      simp only [W,Fintype.sum_prod_type,← Finset.mul_sum,hKs,mul_one,hws]
    have hWmarg (f : Fin (h+2) → ℝ) :
        (∑ ij, W ij*f ij.2)=∑ j, (h+2:ℝ)⁻¹*f j := by
      simp only [W,Fintype.sum_prod_type,mul_assoc,← Finset.mul_sum]
      rw [hmarg (fun i : Fin (h+1) => ∑ j, K i j*f j)]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      simp only [← mul_assoc,← Finset.sum_mul,hKcol]
    have hWmean : (∑ ij, (W ij:ℂ)*Z ij (h+1))=r 0 0 := by
      simp only [W,Fintype.sum_prod_type,Complex.ofReal_mul,hZEnd,mul_assoc,
        ← Finset.mul_sum,hKm]
      simpa only [← hend] using hmean
    have hαe (i : κ) : (∑ j, K (last i) j*‖r (h+1) j-z i h‖^2) =
        (∑ j, K (last i) j*‖r (h+1) j-r 0 0‖^2)-‖z i h-r 0 0‖^2 := by
      have ht := _root_.DerivativeChainContinuation.finite_weighted_variance (K (last i)) (r (h+1)) (r h (last i))
        (r 0 0) (hKs (last i)) (hKm (last i))
      rw [← hend] at ht
      linarith
    have hEn : (∑ ij, W ij*_root_.DerivativeChainContinuation.historyEnergy (h+1) (Z ij)) =
        (∑ ij, W ij*‖Z ij (h+1)-r 0 0‖^2) := by
      have hcalc : (∑ ij, W ij*_root_.DerivativeChainContinuation.historyEnergy (h+1) (Z ij)) =
          (∑ i, w i*_root_.DerivativeChainContinuation.historyEnergy h (z i)) +
          (∑ i, w i*(∑ j, K (last i) j*‖r (h+1) j-r 0 0‖^2)) -
          (∑ i, w i*‖z i h-r 0 0‖^2) := by
        simp only [W,Fintype.sum_prod_type,hZE,mul_add,mul_assoc,Finset.sum_add_distrib,
          ← Finset.mul_sum,← Finset.sum_mul,hKs,one_mul,hαe]
        simp only [mul_sub,Finset.sum_sub_distrib]
        ring
      rw [hcalc,henergy]
      simp only [W,Fintype.sum_prod_type,hZEnd,mul_assoc,← Finset.mul_sum]
      ring
    refine ⟨κ × Fin (h+2),inferInstance,W,Z,Prod.snd,?_,hWs,(fun ij => hZEnd ij.1 ij.2),?_,
      (by intro f; convert hWmarg f using 1 <;> norm_num [Nat.cast_add,Nat.cast_one,add_assoc]),hWmean,hEn⟩
    · intro ij; exact mul_nonneg (hw0 ij.1) (hK _ _)
    · intro ij k hk
      by_cases hkh : k ≤ h
      · simpa only [Z,if_pos hkh] using hroots ij.1 k hkh
      · have he : k=h+1 := by omega
        subst k
        exact ⟨ij.2,by simp [Z]⟩
