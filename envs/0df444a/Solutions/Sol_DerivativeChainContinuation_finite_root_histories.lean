-- Prove2me | solution 1 for DerivativeChainContinuation.finite_root_histories
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:20:19.940753+00:00
-- url     : https://prove2.me/submissions/7bdc22ba-25b3-43f9-b09b-496444fe59d1

import Mathlib
import Definitions.Def_DerivativeChainContinuation_FiniteRootHistories
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChain_root_probability
import Theorems.Thm_DerivativeChainContinuation_finite_weighted_variance
open DerivativeChain DerivativeChainPrivate
open Polynomial
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false




open scoped BigOperators Polynomial

noncomputable section

namespace DerivativeChain



theorem rootProbability_nonneg (P : ℂ[X]) (z : ℂ) (w : P.roots.toFinset) :
    0 ≤ rootProbability P z w := by
  exact div_nonneg (P.derivRootWeight_nonneg z w)
    (Finset.sum_nonneg fun v _ => P.derivRootWeight_nonneg z v)

theorem sum_rootProbability {P : ℂ[X]} (hP : 0 < P.degree) (z : ℂ) :
    ∑ w : P.roots.toFinset, rootProbability P z w = 1 := by
  classical
  simp only [rootProbability, ← Finset.sum_div, Finset.sum_coe_sort]
  exact div_self (Polynomial.sum_derivRootWeight_pos hP z).ne'

theorem rootProbability_mean {P : ℂ[X]} {z : ℂ}
    (hP : 0 < P.degree) (hz : P.derivative.eval z = 0) :
    ∑ w : P.roots.toFinset, rootProbability P z w • (w : ℂ) = z := by
  classical
  simp only [rootProbability, div_eq_inv_mul, mul_smul, ← Finset.smul_sum]
  rw [Finset.sum_coe_sort P.roots.toFinset
    (fun w : ℂ => P.derivRootWeight z w • w)]
  exact (Polynomial.eq_centerMass_of_eval_derivative_eq_zero hP hz).symm





theorem rootProbability_support {P : ℂ[X]} (hP : 0 < P.degree)
    (w : P.roots.toFinset) : P.eval (w : ℂ) = 0 := by
  have hP0 : P ≠ 0 := by rintro rfl; simp at hP
  exact (Polynomial.mem_roots hP0).mp (Multiset.mem_toFinset.mp w.property)





end DerivativeChain



open scoped BigOperators Polynomial

noncomputable section

namespace DerivativeChainPrivate







end DerivativeChainPrivate




end
end


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace DerivativeChainContinuation
open Polynomial
open scoped BigOperators





end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution {ι : Type} [Fintype ι]
    (P : ℕ → Polynomial ℂ) (h : ℕ)
    (hdegree : ∀ k < h, 0 < (P (k+1)).degree)
    (hstep : ∀ k < h, ∀ w : ℂ, (P k).eval w=0 → (P (k+1)).derivative.eval w=0)
    (π : ι → ℝ) (b : ι → ℂ) (u : ℂ) (ρ : ℝ)
    (hπ0 : ∀ i, 0 ≤ π i) (hπsum : ∑ i, π i=1)
    (hπmean : ∑ i, (π i:ℂ)*b i=u) (hb : ∀ i, (P 0).eval (b i)=0)
    (hρ : ∀ i, ‖b i-u‖^2=ρ^2) :
    ∃ (κ : Type) (inst : Fintype κ), letI := inst;
      ∃ (w : κ → ℝ) (z : κ → ℕ → ℂ) (origin : κ → ι),
        (∀ i, 0 ≤ w i) ∧ (∑ i, w i=1) ∧ (∀ i, z i 0=b (origin i)) ∧
        (∀ i k, k ≤ h → (P k).eval (z i k)=0) ∧
        (∑ i, (w i:ℂ)*z i h=u) ∧
        (∑ i, w i*historyEnergy h (z i))=(∑ i, w i*‖z i h-u‖^2)-ρ^2 := by
  classical
  induction h with
  | zero =>
    refine ⟨ι,inferInstance,π,(fun i _ => b i),id,hπ0,hπsum,?_,?_,hπmean,?_⟩
    · intro i; rfl
    · intro i k hk
      have he : k=0 := by omega
      subst k
      exact hb i
    · simp only [historyEnergy,Finset.sum_range_zero,mul_zero,Finset.sum_const_zero,hρ,
        ← Finset.sum_mul,hπsum,one_mul,sub_self]
  | succ h ih =>
    obtain ⟨κ,inst,hdata⟩ := ih (fun k hk => hdegree k (by omega))
      (fun k hk => hstep k (by omega))
    letI : Fintype κ := inst
    obtain ⟨w,z,origin,hw0,hws,hz0,hzr,hzm,hze⟩ := hdata
    let F := P (h+1)
    let J := F.roots.toFinset
    have hF : 0 < F.degree := hdegree h (by omega)
    let α : κ → J → ℝ := fun i j => DerivativeChain.rootProbability F (z i h) j
    have hα0 (i : κ) (j : J) : 0 ≤ α i j := DerivativeChain.rootProbability_nonneg F (z i h) j
    have hαs (i : κ) : ∑ j, α i j=1 := DerivativeChain.sum_rootProbability hF (z i h)
    have hαm (i : κ) : ∑ j : J, (α i j:ℂ)*(j:ℂ)=z i h := by
      have hc : F.derivative.eval (z i h)=0 := hstep h (by omega) (z i h) (hzr i h le_rfl)
      simpa only [Complex.real_smul] using DerivativeChain.rootProbability_mean hF hc
    have hαe (i : κ) : (∑ j : J, α i j*‖(j:ℂ)-z i h‖^2) =
        (∑ j : J, α i j*‖(j:ℂ)-u‖^2)-‖z i h-u‖^2 := by
      have ht := finite_weighted_variance (α i) (fun j : J => (j:ℂ)) (z i h) u (hαs i) (hαm i)
      linarith
    let W : κ × J → ℝ := fun ij => w ij.1*α ij.1 ij.2
    let Z : κ × J → ℕ → ℂ := fun ij k => if k ≤ h then z ij.1 k else (ij.2:ℂ)
    have hZEnd (i : κ) (j : J) : Z (i,j) (h+1)=(j:ℂ) := by simp [Z]
    have hZE (i : κ) (j : J) : historyEnergy (h+1) (Z (i,j)) =
        historyEnergy h (z i)+‖(j:ℂ)-z i h‖^2 := by
      rw [historyEnergy,Finset.sum_range_succ]
      congr 1
      · apply Finset.sum_congr rfl
        intro k hk
        have hk' := Finset.mem_range.mp hk
        simp [Z,show k ≤ h by omega,show k+1 ≤ h by omega]
      · simp [Z]
    have hWs : ∑ ij, W ij=1 := by
      simp only [W,Fintype.sum_prod_type,← Finset.mul_sum,hαs,mul_one,hws]
    have hWmean : ∑ ij, (W ij:ℂ)*Z ij (h+1)=u := by
      simp only [W,Fintype.sum_prod_type,Complex.ofReal_mul,hZEnd,mul_assoc,
        ← Finset.mul_sum,hαm,hzm]
    have hEn : (∑ ij, W ij*historyEnergy (h+1) (Z ij)) =
        (∑ ij, W ij*‖Z ij (h+1)-u‖^2)-ρ^2 := by
      have hcalc : (∑ ij, W ij*historyEnergy (h+1) (Z ij)) =
          (∑ i, w i*historyEnergy h (z i)) +
          (∑ i, w i*(∑ j : J, α i j*‖(j:ℂ)-u‖^2)) -
          (∑ i, w i*‖z i h-u‖^2) := by
        simp only [W,Fintype.sum_prod_type,hZE,mul_assoc]
        simp only [← Finset.mul_sum]
        have hinner (i : κ) : (∑ j : J, α i j*(historyEnergy h (z i)+‖(j:ℂ)-z i h‖^2)) =
            historyEnergy h (z i)+(∑ j : J, α i j*‖(j:ℂ)-u‖^2)-‖z i h-u‖^2 := by
          simp only [mul_add]
          rw [Finset.sum_add_distrib,← Finset.sum_mul,hαs,one_mul,hαe]
          ring
        simp only [hinner]
        simp only [mul_sub,mul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib]
      rw [hcalc,hze]
      simp only [W,Fintype.sum_prod_type,hZEnd,mul_assoc,← Finset.mul_sum]
      ring
    refine ⟨κ × J,inferInstance,W,Z,(fun ij => origin ij.1),?_,hWs,?_,?_,hWmean,hEn⟩
    · intro ij; exact mul_nonneg (hw0 ij.1) (hα0 ij.1 ij.2)
    · intro ij; simpa only [Z,show 0 ≤ h by omega,if_true] using hz0 ij.1
    · intro ij k hk
      by_cases hkh : k ≤ h
      · simpa only [Z,if_pos hkh] using hzr ij.1 k hkh
      · have he : k=h+1 := by omega
        subst k
        simpa only [hZEnd] using DerivativeChain.rootProbability_support hF ij.2
