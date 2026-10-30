-- Prove2me | solution 1 for DerivativeChainContinuation.appell_centroid_return_parameter
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:31:49.388081+00:00
-- url     : https://prove2.me/submissions/18972314-1e7d-4c9b-83ef-ec5b734b2e1c

import Mathlib
import Definitions.Def_DerivativeChainContinuation_AppellRows
import Definitions.Def_DerivativeChainContinuation_AppellTranslation
import Definitions.Def_DerivativeChainContinuation_BinomialRows
import Definitions.Def_DerivativeChainContinuation_FiniteRootHistories
import Definitions.Def_DerivativeChainContinuation_JoinedPaths
import Definitions.Def_DerivativeChainContinuation_ReturnPath
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChain_root_probability
import Theorems.Thm_DerivativeChainContinuation_appellRow_one_mode
import Theorems.Thm_DerivativeChainContinuation_appell_one_mode_geodesic
import Theorems.Thm_DerivativeChainContinuation_binomial_root_law
import Theorems.Thm_DerivativeChainContinuation_closeAt_cost
import Theorems.Thm_DerivativeChainContinuation_finite_history_return_bound
import Theorems.Thm_DerivativeChainContinuation_finite_root_histories
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

theorem derivative_root_norm_le {P : Polynomial ℂ} (hP : 0 < P.degree)
    (R : ℝ) (hR : ∀ w ∈ P.roots, ‖w‖ ≤ R) {z : ℂ}
    (hz : P.derivative.eval z = 0) : ‖z‖ ≤ R := by
  have hp : P ≠ 0 := by rintro rfl; simp at hP
  have hd : P.derivative ≠ 0 := Polynomial.derivative_eq_zero.not.mpr
    (Nat.ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.mpr hP))
  have hm : z ∈ P.derivative.rootSet ℂ := by
    rw [Polynomial.mem_rootSet, Polynomial.coe_aeval_eq_eval]
    exact ⟨hd, hz⟩
  have hs : P.rootSet ℂ ⊆ Metric.closedBall (0 : ℂ) R := by
    intro w hw
    rw [Polynomial.mem_rootSet, Polynomial.coe_aeval_eq_eval] at hw
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      hR w ((Polynomial.mem_roots hp).mpr hw.2)
  have hmem := (convexHull_min hs (convex_closedBall (0 : ℂ) R))
    (P.rootSet_derivative_subset_convexHull_rootSet hP hm)
  simpa only [Metric.mem_closedBall, dist_zero_right] using hmem







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









theorem iterate_derivative_norm_bound (p : Polynomial ℂ) (k : ℕ) (hk : k < p.natDegree)
    (M : ℝ) (hbound : ∀ z, p.eval z = 0 → ‖z‖ ≤ M) (z : ℂ)
    (hz : (derivative^[k] p).eval z = 0) : ‖z‖ ≤ M := by
  induction k generalizing p with
  | zero => exact hbound z hz
  | succ k ih =>
    have hkd : k < p.derivative.natDegree := by rw [natDegree_derivative]; omega
    have hpne : p ≠ 0 := by intro h; simp [h] at hk
    have hpd : 0 < p.degree := natDegree_pos_iff_degree_pos.mp (by omega)
    have hdbound : ∀ w, p.derivative.eval w = 0 → ‖w‖ ≤ M := by
      intro w hw
      exact derivative_root_norm_le hpd M
        (fun z hz => hbound z ((mem_roots hpne).mp hz)) hw
    rw [Function.iterate_succ_apply] at hz
    exact ih p.derivative hkd hdbound hz

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



theorem binomialPoly_eval_root (q r : ℕ) (c b : ℂ) (hb : b^q= -c) :
    (binomialPoly q r c).eval b=0 := by
  simp only [binomialPoly,eval_add,eval_pow,eval_X,eval_mul,eval_C,pow_add,hb]
  ring





end DerivativeChainContinuation



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





end DerivativeChainContinuation



set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate

theorem translatedAppell_shift_eval (m : ℕ) (c : ℕ → ℂ) (u a z : ℂ) :
    (translatedAppell m c (u-a)).eval (z-a)=(translatedAppell m c u).eval z := by
  rw [translatedAppell_eval,translatedAppell_eval]
  congr 1
  ring

theorem appell_row_disk_bound (n m : ℕ) (hm : 0 < m) (hmn : m ≤ n)
    (c : ℕ → ℂ) (hc0 : c 0=1) (u a : ℂ) (D : ℝ)
    (hbound : ∀ z : ℂ, (translatedAppell n c u).eval z=0 → ‖z-a‖ ≤ D)
    (z : ℂ) (hz : (translatedAppell m c u).eval z=0) : ‖z-a‖ ≤ D := by
  have hsrc (w : ℂ) (hw : (translatedAppell n c (u-a)).eval w=0) : ‖w‖ ≤ D := by
    have he : (translatedAppell n c u).eval (w+a)=0 := by
      rw [← translatedAppell_shift_eval n c u a (w+a)]
      simpa using hw
    simpa using hbound (w+a) he
  have hz' : (translatedAppell m c (u-a)).eval (z-a)=0 := by
    rwa [translatedAppell_shift_eval]
  exact iterate_derivative_norm_bound (translatedAppell n c (u-a)) (n-m)
    (by rw [translatedAppell_natDegree n c (u-a) hc0]; omega) D hsrc (z-a)
    (translatedAppell_actual_root n m hmn c (u-a) (z-a) hz')

end DerivativeChainContinuation



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators



end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (M h s q d : ℕ) (hq : 2 ≤ q) (hqM : q ≤ M)
    (hs : 0 < s) (c : ℕ → ℂ) (hc0 : c 0=1)
    (hpref : ∀ j ≤ M, j ≠ 0 → j ≠ q → c j=0)
    (hreturn : ∀ j, M+h < j → j ≤ M+h+s → c j=0)
    (hd : d=h+1 ∨ (d=h ∧ c q=0))
    (u a : ℂ) (D : ℝ) (hD : 0 ≤ D)
    (hbound : ∀ z : ℂ, (translatedAppell (M+h+s) c u).eval z=0 → ‖z-a‖ ≤ D) :
    ∃ z : Fin (M+h+s) → ℂ,
      (∀ i, (derivative^[M+h+s-(i.val+1)] (translatedAppell (M+h+s) c u)).eval (z i)=0) ∧
      z ⟨0,by omega⟩=u ∧ (∀ i, M+h ≤ i.val → z i=u) ∧
      chainCost z ≤ (1+Real.sqrt d)*Real.sqrt (D^2-‖u-a‖^2) := by
  classical
  have hM : 1 ≤ M := by omega
  let η := (M.choose q:ℂ)*c q
  let F : Polynomial ℂ := X^q+C η
  let I := F.roots.toFinset
  let ρ := ‖η‖^((q:ℝ)⁻¹)
  have hρ0 : 0 ≤ ρ := Real.rpow_nonneg (norm_nonneg η) _
  obtain ⟨π,hπ0,hπs,hπm,hpow,hnorm⟩ := binomial_root_law q hq η
  have hg (i : I) : ∃ f : ℕ → ℂ, f 0=0 ∧ f (M-1)=(i:ℂ) ∧
      (∀ k < M, (appellRow (k+1) c).eval (f k)=0) ∧
      (∀ k < M-1, ‖f (k+1)-f k‖ = ‖f (k+1)‖-‖f k‖) :=
    appell_one_mode_geodesic M q hq hqM c hc0 hpref i (hpow i)
  choose f hf0 hfend hfroot hfstep using hg
  let P : ℕ → Polynomial ℂ := fun k => translatedAppell (M+k) c u
  have hPdeg (k : ℕ) (_ : k < h) : 0 < (P (k+1)).degree := by
    apply natDegree_pos_iff_degree_pos.mp
    rw [translatedAppell_natDegree _ c u hc0]
    omega
  have hPstep (k : ℕ) (_ : k < h) (z : ℂ) (hz : (P k).eval z=0) :
      (P (k+1)).derivative.eval z=0 := by
    dsimp only [P] at hz ⊢
    rw [show M+(k+1)=(M+k)+1 by omega,translatedAppell_derivative,eval_mul,hz,mul_zero]
  let b : I → ℂ := fun i => u+(i:ℂ)
  have hb (i : I) : (P 0).eval (b i)=0 := by
    simp only [P,Nat.add_zero,b,translatedAppell_eval,add_sub_cancel_left]
    rw [appellRow_one_mode M q (by omega) hqM c hc0 hpref]
    exact binomialPoly_eval_root q (M-q) η i (hpow i)
  have hbm : ∑ i, (π i:ℂ)*b i=u := by
    simp only [b,mul_add,Finset.sum_add_distrib,← Finset.sum_mul,← Complex.ofReal_sum,hπs,hπm]
    simp
  have hbr (i : I) : ‖b i-u‖^2=ρ^2 := by simp only [b,add_sub_cancel_left,hnorm,ρ]
  obtain ⟨κ,inst,hdata⟩ := finite_root_histories P h hPdeg hPstep π b u ρ hπ0 hπs hbm hb hbr
  letI : Fintype κ := inst
  obtain ⟨w,z,origin,hw0,hws,hz0,hzr,hzm,hze⟩ := hdata
  let inner : κ → ℕ → ℂ := fun i => joinAt M (fun k => u+f (origin i) k) (z i)
  have hconnect (i : κ) : u+f (origin i) (M-1)=z i 0 := by
    rw [hfend,hz0]
  have hilast (i : κ) : inner i (M+h-1)=z i h := by
    rw [show M+h-1=M-1+h by omega]
    exact joinAt_tail M hM _ _ (hconnect i) h
  have hiroot (i : κ) (k : ℕ) (hk : k < M+h) :
      (translatedAppell (k+1) c u).eval (inner i k)=0 := by
    by_cases hkm : k < M
    · simp only [inner,joinAt,if_pos hkm,translatedAppell_eval,add_sub_cancel_left]
      exact hfroot (origin i) k hkm
    · have hj : k-(M-1) ≤ h := by omega
      have he : M+(k-(M-1))=k+1 := by omega
      simpa only [P,he,inner,joinAt,if_neg hkm] using hzr i (k-(M-1)) hj
  have hicost (i : κ) : chainCost (fun k : Fin (M+h) => inner i k)=
      ρ+∑ k ∈ Finset.range h, ‖z i (k+1)-z i k‖ := by
    rw [joinAt_cost M h hM _ _ (hconnect i)]
    simp only [add_sub_add_left_eq_sub]
    rw [geodesic_prefix_cost M (f (origin i)) (hf0 _) (hfstep _),hfend,hnorm]
  have hend (i : κ) : ‖z i h-a‖ ≤ D :=
    appell_row_disk_bound (M+h+s) (M+h) (by omega) (by omega) c hc0 u a D hbound
      (z i h) (hzr i h le_rfl)
  have hdρ : d=h+1 ∨ (d=h ∧ ρ=0) := by
    rcases hd with hd|⟨hd,hcq⟩
    · exact Or.inl hd
    · refine Or.inr ⟨hd,?_⟩
      simp only [ρ,η,hcq,mul_zero,norm_zero]
      exact Real.zero_rpow (inv_ne_zero (by exact_mod_cast (show q ≠ 0 by omega)))
  obtain ⟨i,hi⟩ := finite_history_return_bound w z h d ρ D u a hw0 hws hρ0 hD hdρ hzm hend hze
  let v : Fin (M+h+s) → ℂ := fun k => closeAt (M+h) (inner i) u k
  refine ⟨v,?_,?_,?_,?_⟩
  · intro k
    apply translatedAppell_actual_root (M+h+s) (k.val+1) (by omega)
    by_cases hk : k.val < M+h
    · simpa only [v,closeAt,if_pos hk] using hiroot i k hk
    · simp only [v,closeAt,if_neg hk,translatedAppell_eval,sub_self,← coeff_zero_eq_eval_zero,appellRow_coeff_eq]
      simp [hreturn (k.val+1) (by omega) (by omega)]
  · simp [v,closeAt,inner,joinAt,show 0 < M+h by omega,show 0 < M by omega,hf0]
  · intro k hk
    simp only [v,closeAt,if_neg (by omega : ¬k.val < M+h)]
  · rw [closeAt_cost (M+h) s (by omega) hs (inner i) u,hicost,hilast,norm_sub_rev u (z i h)]
    exact hi
