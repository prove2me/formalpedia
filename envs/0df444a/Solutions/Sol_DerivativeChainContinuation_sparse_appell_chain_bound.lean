-- Prove2me | solution 1 for DerivativeChainContinuation.sparse_appell_chain_bound
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:57:53.995314+00:00
-- url     : https://prove2.me/submissions/58f5f129-df9a-4256-9271-c7d7b4805758

import Mathlib
import Definitions.Def_DerivativeChainContinuation_AppellRows
import Definitions.Def_DerivativeChainContinuation_AppellTranslation
import Definitions.Def_DerivativeChainContinuation_JoinedPaths
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChain_root_probability
import Theorems.Thm_DerivativeChainContinuation_appell_one_mode_geodesic
import Theorems.Thm_DerivativeChainContinuation_exists_binomial_endpoint_energy
import Theorems.Thm_DerivativeChainContinuation_finite_tail_energy
open DerivativeChain DerivativeChainPrivate
open Polynomial
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Polynomial
open scoped BigOperators







theorem iterate_derivative_translate {R : Type*} [CommRing R] (p : Polynomial R) (u : R) (k : ℕ) :
    (derivative^[k] (p.comp (X+C u)))=(derivative^[k] p).comp (X+C u) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply',ih,derivative_comp]
    simp






end DerivativeChainContinuation



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







theorem chainCost_eq_sum_range {n : ℕ} (f : ℕ → ℂ) :
    chainCost (fun i : Fin n => f i.val) =
      ∑ i ∈ Finset.range (n - 1), ‖f (i + 1) - f i‖ := by
  unfold chainCost
  exact Fin.sum_univ_eq_sum_range (fun i => ‖f (i + 1) - f i‖) (n - 1)





end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
open scoped BigOperators
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





set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial
open scoped BigOperators



theorem appellRow_coeff (m k : ℕ) (c : ℕ → ℂ) :
    (appellRow m c).coeff k = if k ≤ m then (m.choose k:ℂ)*c (m-k) else 0 := by
  classical
  simp only [appellRow,finsetSum_coeff,coeff_C_mul,coeff_X_pow,mul_ite,mul_one,mul_zero]
  simp [Finset.sum_ite_eq',Nat.lt_succ_iff]

theorem appellRow_coeff_eq (m k : ℕ) (c : ℕ → ℂ) :
    (appellRow m c).coeff k = (m.choose k:ℂ)*c (m-k) := by
  rw [appellRow_coeff]
  split_ifs with hk
  · rfl
  · rw [Nat.choose_eq_zero_of_lt (by omega),Nat.cast_zero,zero_mul]

theorem appellRow_natDegree_le (m : ℕ) (c : ℕ → ℂ) : (appellRow m c).natDegree ≤ m := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [appellRow_coeff,if_neg (by omega)]



theorem appellRow_natDegree (m : ℕ) (c : ℕ → ℂ) (hc : c 0=1) :
    (appellRow m c).natDegree=m := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (appellRow_natDegree_le m c)
  simp [appellRow_coeff_eq,hc]

theorem appellRow_derivative (m : ℕ) (c : ℕ → ℂ) :
    (appellRow (m+1) c).derivative = C (m+1:ℂ)*appellRow m c := by
  ext k
  rw [coeff_derivative,coeff_C_mul,appellRow_coeff_eq,appellRow_coeff_eq]
  have hch : (m+1:ℂ)*(m.choose k:ℂ) = ((m+1).choose (k+1):ℂ)*(k+1:ℂ) := by
    exact_mod_cast Nat.add_one_mul_choose_eq m k
  rw [show m+1-(k+1)=m-k by omega]
  push_cast
  linear_combination -c (m-k)*hch

theorem appellRow_iterate_derivative (m k : ℕ) (c : ℕ → ℂ) :
    derivative^[k] (appellRow (m+k) c) = C ((m+k).descFactorial k:ℂ)*appellRow m c := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show m+Nat.succ k=(m+k)+1 by omega,Function.iterate_succ_apply,
      appellRow_derivative,iterate_derivative_C_mul,ih,← mul_assoc,← C_mul]
    rw [Nat.succ_descFactorial_succ]
    push_cast
    rfl

end DerivativeChainContinuation



set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial



theorem translatedAppell_natDegree (m : ℕ) (c : ℕ → ℂ) (u : ℂ) (hc : c 0=1) :
    (translatedAppell m c u).natDegree=m := by
  simp [translatedAppell,natDegree_comp,appellRow_natDegree m c hc]

theorem translatedAppell_eval (m : ℕ) (c : ℕ → ℂ) (u z : ℂ) :
    (translatedAppell m c u).eval z=(appellRow m c).eval (z-u) := by
  simp [translatedAppell]

theorem translatedAppell_derivative (m : ℕ) (c : ℕ → ℂ) (u : ℂ) :
    (translatedAppell (m+1) c u).derivative=C (m+1:ℂ)*translatedAppell m c u := by
  simp [translatedAppell,derivative_comp,appellRow_derivative,mul_comp]

theorem translatedAppell_actual_root (n m : ℕ) (hm : m ≤ n) (c : ℕ → ℂ)
    (u z : ℂ) (hz : (translatedAppell m c u).eval z=0) :
    (derivative^[n-m] (translatedAppell n c u)).eval z=0 := by
  have hd := appellRow_iterate_derivative m (n-m) c
  rw [show m+(n-m)=n by omega] at hd
  have ht := iterate_derivative_translate (appellRow n c) (-u) (n-m)
  simp only [map_neg,← sub_eq_add_neg] at ht
  rw [translatedAppell,ht,hd,mul_comp,C_comp,eval_mul,eval_C]
  exact mul_eq_zero_of_right _ hz

end DerivativeChainContinuation



set_option autoImplicit false
namespace DerivativeChainContinuation
open DerivativeChainPrivate
open scoped BigOperators



theorem joinAt_tail (M : ℕ) (hM : 1 ≤ M) (f z : ℕ → ℂ)
    (he : f (M-1)=z 0) (j : ℕ) : joinAt M f z (M-1+j)=z j := by
  by_cases hj : j=0
  · subst j; simp [joinAt,show M-1 < M by omega,he]
  · simp [joinAt,show ¬M-1+j < M by omega]

theorem joinAt_cost (M h : ℕ) (hM : 1 ≤ M) (f z : ℕ → ℂ)
    (he : f (M-1)=z 0) :
    chainCost (fun i : Fin (M+h) => joinAt M f z i) =
      (∑ i ∈ Finset.range (M-1), ‖f (i+1)-f i‖) +
      (∑ j ∈ Finset.range h, ‖z (j+1)-z j‖) := by
  rw [chainCost_eq_sum_range,show M+h-1=(M-1)+h by omega,Finset.sum_range_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    simp [joinAt,show i < M by omega,show i+1 < M by omega]
  · apply Finset.sum_congr rfl
    intro j _
    rw [show M-1+j+1=M-1+(j+1) by omega,joinAt_tail M hM f z he,joinAt_tail M hM f z he]

theorem geodesic_prefix_cost (M : ℕ) (f : ℕ → ℂ) (hf0 : f 0=0)
    (hstep : ∀ i < M-1, ‖f (i+1)-f i‖ = ‖f (i+1)‖-‖f i‖) :
    (∑ i ∈ Finset.range (M-1), ‖f (i+1)-f i‖) = ‖f (M-1)‖ := by
  calc
    _ = ∑ i ∈ Finset.range (M-1), (‖f (i+1)‖-‖f i‖) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hstep i (Finset.mem_range.mp hi)
    _ = _ := by rw [Finset.sum_range_sub (fun i => ‖f i‖),hf0,norm_zero,sub_zero]

theorem compressed_prefix_cauchy (h : ℕ) (r : ℝ) (l : ℕ → ℝ) :
    (r+∑ j ∈ Finset.range h, l j)^2 ≤
      (h+1 : ℝ)*(r^2+∑ j ∈ Finset.range h, (l j)^2) := by
  let f : Fin (h+1) → ℝ := Fin.cases r (fun j => l j)
  have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin (h+1) => (1:ℝ)) f
  have he : (∑ j : Fin h, (l j)^2) = ∑ j ∈ Finset.range h, (l j)^2 :=
    Fin.sum_univ_eq_sum_range (fun j => (l j)^2) h
  simpa [f,Fin.sum_univ_succ,Fin.sum_univ_eq_sum_range,he] using hh



end DerivativeChainContinuation



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators




end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (M h q : ℕ) (hq : 2 ≤ q) (hqM : q ≤ M)
    (c : ℕ → ℂ) (hc0 : c 0=1)
    (hs : ∀ j ≤ M, j ≠ 0 → j ≠ q → c j=0)
    (u : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ z : ℂ, (translatedAppell (M+h) c u).eval z=0 → ‖z‖ ≤ R) :
    ∃ z : Fin (M+h) → ℂ,
      (∀ i, (derivative^[M+h-(i.val+1)] (translatedAppell (M+h) c u)).eval (z i)=0) ∧
      z ⟨0,by omega⟩=u ∧ chainCost z ≤ Real.sqrt (h+1)*Real.sqrt (R^2-‖u‖^2) ∧
      (c q=0 → chainCost z ≤ Real.sqrt h*Real.sqrt (R^2-‖u‖^2)) := by
  have hM : 1 ≤ M := by omega
  obtain ⟨b,hb,hbenergy⟩ := exists_binomial_endpoint_energy q hq ((M.choose q:ℂ)*c q) u
  obtain ⟨f,hf0,hfend,hfroot,hfstep⟩ := appell_one_mode_geodesic M q hq hqM c hc0 hs b hb
  let g : ℕ → ℂ := fun i => u+f i
  have hgroot (i : ℕ) (hi : i < M) : (translatedAppell (i+1) c u).eval (g i)=0 := by
    rw [translatedAppell_eval]
    simpa only [g,add_sub_cancel_left] using hfroot i hi
  let P : ℕ → Polynomial ℂ := fun j => translatedAppell (M+j) c u
  have hPdeg (j : ℕ) (_ : j < h) : 0 < (P (j+1)).degree := by
    apply natDegree_pos_iff_degree_pos.mp
    rw [translatedAppell_natDegree _ c u hc0]
    omega
  have hPstep (j : ℕ) (_ : j < h) (w : ℂ) (hw : (P j).eval w=0) :
      (P (j+1)).derivative.eval w=0 := by
    dsimp only [P] at hw ⊢
    rw [show M+(j+1)=(M+j)+1 by omega,translatedAppell_derivative,eval_mul,hw,mul_zero]
  have hstart : (P 0).eval (u+b)=0 := by
    have hh := hgroot (M-1) (by omega)
    simpa only [P,Nat.add_zero,show M-1+1=M by omega,g,hfend] using hh
  obtain ⟨t,ht0,htroot,htenergy⟩ := finite_tail_energy P h hPdeg hPstep (u+b) hstart
  have he : g (M-1)=t 0 := by simp only [g,hfend,ht0]
  let w : Fin (M+h) → ℂ := fun i => joinAt M g t i
  have hwroot (i : Fin (M+h)) :
      (derivative^[M+h-(i.val+1)] (translatedAppell (M+h) c u)).eval (w i)=0 := by
    apply translatedAppell_actual_root (M+h) (i.val+1) (by omega)
    by_cases hi : i.val < M
    · simpa only [w,joinAt,if_pos hi] using hgroot i hi
    · have hj : i.val-(M-1) ≤ h := by omega
      have hrow : M+(i.val-(M-1))=i.val+1 := by omega
      have hh := htroot (i.val-(M-1)) hj
      simpa only [P,hrow,w,joinAt,if_neg hi] using hh
  have hpref : (∑ i ∈ Finset.range (M-1), ‖g (i+1)-g i‖)=‖b‖ := by
    simp only [g,add_sub_add_left_eq_sub]
    rw [geodesic_prefix_cost M f hf0 hfstep,hfend]
  have hcost : chainCost w=‖b‖+∑ j ∈ Finset.range h, ‖t (j+1)-t j‖ := by
    rw [joinAt_cost M h hM g t he,hpref]
  have hfinal := hbound (t h) (htroot h le_rfl)
  have hfinalSq : ‖t h‖^2 ≤ R^2 := (sq_le_sq₀ (norm_nonneg _) hR).mpr hfinal
  have htail0 : 0 ≤ ∑ j ∈ Finset.range h, ‖t (j+1)-t j‖^2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  have henergy : ‖b‖^2+(∑ j ∈ Finset.range h, ‖t (j+1)-t j‖^2) ≤ R^2-‖u‖^2 := by
    linarith
  have hvariance : 0 ≤ R^2-‖u‖^2 := by nlinarith [sq_nonneg ‖b‖]
  have hsq : chainCost w^2 ≤ (h+1:ℝ)*(R^2-‖u‖^2) := by
    rw [hcost]
    exact (compressed_prefix_cauchy h ‖b‖ (fun j => ‖t (j+1)-t j‖)).trans
      (mul_le_mul_of_nonneg_left henergy (by positivity))
  have hright : (Real.sqrt (h+1)*Real.sqrt (R^2-‖u‖^2))^2=(h+1:ℝ)*(R^2-‖u‖^2) := by
    rw [mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt hvariance]
  refine ⟨w,hwroot,?_,?_,?_⟩
  · simp [w,joinAt,show 0 < M by omega,g,hf0]
  · rw [← hright] at hsq
    exact (sq_le_sq₀ (by unfold chainCost; positivity) (by positivity)).mp hsq

  · intro hcq
    have hb0 : b=0 := by
      have hh : b^q=0 := by simpa [hcq] using hb
      exact (pow_eq_zero_iff (by omega : q ≠ 0)).mp hh
    have hcost' : chainCost w=∑ j ∈ Finset.range h, ‖t (j+1)-t j‖ := by simpa [hb0] using hcost
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range h) (fun _ => (1:ℝ))
      (fun j => ‖t (j+1)-t j‖)
    simp only [one_mul,one_pow,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one] at hcs
    have hen : (∑ j ∈ Finset.range h, ‖t (j+1)-t j‖^2) ≤ R^2-‖u‖^2 := by
      simpa [hb0] using henergy
    have hbnd : chainCost w^2 ≤ (h:ℝ)*(R^2-‖u‖^2) := by
      rw [hcost']
      exact hcs.trans (mul_le_mul_of_nonneg_left hen (Nat.cast_nonneg _))
    have hrhs : (Real.sqrt h*Real.sqrt (R^2-‖u‖^2))^2=(h:ℝ)*(R^2-‖u‖^2) := by
      rw [mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt hvariance]
    rw [← hrhs] at hbnd
    exact (sq_le_sq₀ (by unfold chainCost; positivity) (by positivity)).mp hbnd
