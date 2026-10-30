-- Prove2me | solution 1 for DerivativeChainExtremal.actual_balanced_radial_prefix_extension
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T00:49:21.926247+00:00
-- url     : https://prove2.me/submissions/fbb8cd18-78e6-498a-bc28-96bc905c093c

import Mathlib
import Definitions.Def_DerivativeChainContinuation_FiniteRootHistories
import Definitions.Def_DerivativeChainContinuation_JoinedPaths
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_finite_root_histories
import Theorems.Thm_DerivativeChainContinuation_finite_weighted_variance
import Theorems.Thm_DerivativeChainPrivate_exists_nonpos_of_probability_mean_zero
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
open scoped BigOperators





theorem finite_weighted_exists_le_mean {ι : Type} [Fintype ι]
    (w f : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i=1) :
    ∃ i, f i ≤ ∑ j, w j*f j := by
  have he : (∑ i, w i*(f i-∑ j, w j*f j))=0 := by
    simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hs,one_mul,sub_self]
  obtain ⟨i,hi⟩ := DerivativeChainPrivate.exists_nonpos_of_probability_mean_zero w _ hw hs he
  exact ⟨i,by linarith⟩

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



theorem compressed_prefix_cauchy (h : ℕ) (r : ℝ) (l : ℕ → ℝ) :
    (r+∑ j ∈ Finset.range h, l j)^2 ≤
      (h+1 : ℝ)*(r^2+∑ j ∈ Finset.range h, (l j)^2) := by
  let f : Fin (h+1) → ℝ := Fin.cases r (fun j => l j)
  have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin (h+1) => (1:ℝ)) f
  have he : (∑ j : Fin h, (l j)^2) = ∑ j ∈ Finset.range h, (l j)^2 :=
    Fin.sum_univ_eq_sum_range (fun j => (l j)^2) h
  simpa [f,Fin.sum_univ_succ,Fin.sum_univ_eq_sum_range,he] using hh

theorem chainCost_cast_index {n m : ℕ} (h : n=m) (z : Fin m → ℂ) :
    chainCost (fun i : Fin n => z (Fin.cast h i))=chainCost z := by
  subst m
  rfl

end DerivativeChainContinuation


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators













theorem complex_iterate_derivative_natDegree (p : Polynomial ℂ) (j : ℕ) :
    (derivative^[j] p).natDegree=p.natDegree-j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply',natDegree_derivative,ih]
    omega










end DerivativeChainContinuation


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators

theorem actual_complex_source_natDegree {n : ℕ} (a : Fin (n+1) → ℂ) :
    (fromRoots a).natDegree=n+1 := by
  simp only [fromRoots]
  rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C (a i))]
  simp

theorem actual_complex_row_natDegree {n : ℕ} (a : Fin (n+1) → ℂ)
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n+1) : (row a m).natDegree=m := by
  rw [row,complex_iterate_derivative_natDegree,actual_complex_source_natDegree]
  omega













theorem actual_ordinary_row_derivative {n : ℕ} (a : Fin (n+1) → ℂ)
    (m : ℕ) (hmn : m ≤ n) : (row a (m+1)).derivative=row a m := by
  unfold row
  rw [show n+1-m=(n+1-(m+1))+1 by omega,Function.iterate_succ_apply']








end DerivativeChainContinuation


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
open DerivativeChainExtremal
open Polynomial DerivativeChainPrivate DerivativeChainContinuation
open scoped BigOperators

theorem solution {n : ℕ} (a : Fin (n+1) → ℂ)
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n+1) (u o : ℂ) (R ρ : ℝ)
    (hR : 0 ≤ R) (hρ : 0 ≤ ρ) (ha : ∀ i, ‖a i-o‖ ≤ R)
    {ι : Type} [Fintype ι] (π : ι → ℝ) (f : ι → ℕ → ℂ)
    (hπ0 : ∀ i, 0 ≤ π i) (hπsum : ∑ i, π i=1)
    (hf0 : ∀ i, f i 0=u)
    (hfroot : ∀ i j, j < m → (_root_.DerivativeChainPrivate.row a (j+1)).eval (f i j)=0)
    (hfradius : ∀ i, ‖f i (m-1)-u‖=ρ)
    (hfmean : ∑ i, (π i:ℂ)*f i (m-1)=u)
    (hfcost : ∀ i, (∑ j∈Finset.range (m-1), ‖f i (j+1)-f i j‖)=ρ) :
    ∃ z : Fin (n+1) → ℂ, _root_.DerivativeChainPrivate.IsChain a z ∧ z 0=u ∧
      _root_.DerivativeChainPrivate.chainCost z ≤ Real.sqrt (n+1-m+1 : ℕ)*Real.sqrt (R^2-‖u-o‖^2) := by
  classical
  let d := n+1-m
  have hN : m+d=n+1 := by dsimp [d]; omega
  let P : ℕ → Polynomial ℂ := fun j => _root_.DerivativeChainPrivate.row a (m+j)
  have hPdeg (j : ℕ) (hj : j < d) : 0 < (P (j+1)).degree := by
    apply natDegree_pos_iff_degree_pos.mp
    change 0 < (_root_.DerivativeChainPrivate.row a (m+(j+1))).natDegree
    rw [_root_.DerivativeChainContinuation.actual_complex_row_natDegree a _ (by omega) (by omega)]
    omega
  have hPstep (j : ℕ) (hj : j < d) (w : ℂ) (hw : (P j).eval w=0) :
      (P (j+1)).derivative.eval w=0 := by
    dsimp only [P] at hw ⊢
    rw [show m+(j+1)=(m+j)+1 by omega,_root_.DerivativeChainContinuation.actual_ordinary_row_derivative a (m+j) (by omega)]
    exact hw
  have hb (i : ι) : (P 0).eval (f i (m-1))=0 := by
    have h := hfroot i (m-1) (by omega)
    simpa only [P,Nat.add_zero,show m-1+1=m by omega] using h
  have hradius (i : ι) : ‖f i (m-1)-u‖^2=ρ^2 := by rw [hfradius]
  obtain ⟨κ,inst,hdata⟩ := _root_.DerivativeChainContinuation.finite_root_histories P d hPdeg hPstep π
    (fun i => f i (m-1)) u ρ hπ0 hπsum hfmean hb hradius
  letI : Fintype κ := inst
  obtain ⟨w,z,origin,hw0,hws,hz0,hzr,hzm,hze⟩ := hdata
  let W : κ → Fin (m+d) → ℂ := fun i j => _root_.DerivativeChainContinuation.joinAt m (f (origin i)) (z i) j
  let v : κ → Fin (n+1) → ℂ := fun i j => W i (Fin.cast hN.symm j)
  have hcost (i : κ) : _root_.DerivativeChainPrivate.chainCost (v i)=ρ+∑ j∈Finset.range d, ‖z i (j+1)-z i j‖ := by
    change _root_.DerivativeChainPrivate.chainCost (fun j => W i (Fin.cast hN.symm j))=_
    rw [_root_.DerivativeChainContinuation.chainCost_cast_index hN.symm (W i)]
    change _root_.DerivativeChainPrivate.chainCost (fun j : Fin (m+d) => _root_.DerivativeChainContinuation.joinAt m (f (origin i)) (z i) j)=_
    rw [_root_.DerivativeChainContinuation.joinAt_cost m d hm _ _ (hz0 i).symm,hfcost]
  have hactual (i : κ) : _root_.DerivativeChainPrivate.IsChain a (v i) := by
    intro j
    change (_root_.DerivativeChainPrivate.row a (j.val+1)).eval (_root_.DerivativeChainContinuation.joinAt m (f (origin i)) (z i) j.val)=0
    by_cases hj : j.val < m
    · simpa only [_root_.DerivativeChainContinuation.joinAt,if_pos hj] using hfroot (origin i) j.val hj
    · have ht : j.val-(m-1) ≤ d := by omega
      have he : m+(j.val-(m-1))=j.val+1 := by omega
      have hh := hzr i (j.val-(m-1)) ht
      simpa only [P,he,_root_.DerivativeChainContinuation.joinAt,if_neg hj] using hh
  have hstart (i : κ) : v i 0=u := by
    change _root_.DerivativeChainContinuation.joinAt m (f (origin i)) (z i) 0=u
    simp only [_root_.DerivativeChainContinuation.joinAt,if_pos (show 0 < m by omega),hf0]
  have hendroot (i : κ) : (_root_.DerivativeChainPrivate.fromRoots a).eval (z i d)=0 := by
    have h := hzr i d le_rfl
    simpa only [P,hN,_root_.DerivativeChainPrivate.row,Nat.sub_self,Function.iterate_zero_apply] using h
  have hdisk (i : κ) : ‖z i d-o‖ ≤ R := by
    have h := hendroot i
    simp only [_root_.DerivativeChainPrivate.fromRoots,eval_prod,eval_sub,eval_X,eval_C] at h
    obtain ⟨j,_,hj⟩ := Finset.prod_eq_zero_iff.mp h
    rw [sub_eq_zero.mp hj]
    exact ha j
  have havgdisk : (∑ i, w i*‖z i d-o‖^2) ≤ R^2 := by
    calc
      _ ≤ ∑ i, w i*R^2 := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) hR).mpr (hdisk i)) (hw0 i)
      _ = _ := by rw [←Finset.sum_mul,hws,one_mul]
  have hvariance := _root_.DerivativeChainContinuation.finite_weighted_variance w (fun i => z i d) u o hws hzm
  have hvar : (∑ i, w i*‖z i d-u‖^2) ≤ R^2-‖u-o‖^2 := by linarith
  have hV : 0 ≤ R^2-‖u-o‖^2 :=
    (Finset.sum_nonneg fun i _ => mul_nonneg (hw0 i) (sq_nonneg _)).trans hvar
  have hpoint (i : κ) : (_root_.DerivativeChainPrivate.chainCost (v i))^2 ≤
      (d+1:ℝ)*(ρ^2+_root_.DerivativeChainContinuation.historyEnergy d (z i)) := by
    rw [hcost]
    exact _root_.DerivativeChainContinuation.compressed_prefix_cauchy d ρ (fun j => ‖z i (j+1)-z i j‖)
  have havg : (∑ i, w i*(_root_.DerivativeChainPrivate.chainCost (v i))^2) ≤ (d+1:ℝ)*(R^2-‖u-o‖^2) := by
    calc
      _ ≤ ∑ i, w i*((d+1:ℝ)*(ρ^2+_root_.DerivativeChainContinuation.historyEnergy d (z i))) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hpoint i) (hw0 i)
      _ = (d+1:ℝ)*(ρ^2+∑ i, w i*_root_.DerivativeChainContinuation.historyEnergy d (z i)) := by
        have he (i : κ) : w i*((d+1:ℝ)*(ρ^2+_root_.DerivativeChainContinuation.historyEnergy d (z i))) =
            ((d+1:ℝ)*ρ^2)*w i+(d+1:ℝ)*(w i*_root_.DerivativeChainContinuation.historyEnergy d (z i)) := by ring
        simp only [he,Finset.sum_add_distrib,←Finset.mul_sum,hws,mul_one]
        ring
      _ = (d+1:ℝ)*(∑ i, w i*‖z i d-u‖^2) := by rw [hze]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hvar (by positivity)
  obtain ⟨i,hi⟩ := _root_.DerivativeChainContinuation.finite_weighted_exists_le_mean w (fun i => (_root_.DerivativeChainPrivate.chainCost (v i))^2) hw0 hws
  have hsq : (_root_.DerivativeChainPrivate.chainCost (v i))^2 ≤ (d+1:ℝ)*(R^2-‖u-o‖^2) := hi.trans havg
  have hrhs : (Real.sqrt (d+1)*Real.sqrt (R^2-‖u-o‖^2))^2=(d+1:ℝ)*(R^2-‖u-o‖^2) := by
    rw [mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt hV]
  rw [←hrhs] at hsq
  refine ⟨v i,hactual i,hstart i,?_⟩
  have hbound := (sq_le_sq₀ (by unfold _root_.DerivativeChainPrivate.chainCost; positivity) (by positivity)).mp hsq
  simpa only [d,Nat.cast_add,Nat.cast_one] using hbound
