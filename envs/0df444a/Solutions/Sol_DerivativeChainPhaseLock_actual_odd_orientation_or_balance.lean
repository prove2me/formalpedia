-- Prove2me | solution 1 for DerivativeChainPhaseLock.actual_odd_orientation_or_balance
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T06:19:23.532662+00:00
-- url     : https://prove2.me/submissions/e454c7de-bdeb-49ce-9cec-79daf9f72929

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_MomentErrorBounds
import Definitions.Def_DerivativeChainAnalytic_OddMomentPersistence
import Definitions.Def_DerivativeChainContinuation_AppellCoefficients
import Definitions.Def_DerivativeChainContinuation_AppellRows
import Theorems.Thm_DerivativeChainPhaseLock_cluster_moment_error
import Theorems.Thm_DerivativeChainPhaseLock_disk_phase_control
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

theorem appellRow_monic (m : ℕ) (c : ℕ → ℂ) (hc : c 0=1) : (appellRow m c).Monic := by
  apply monic_of_natDegree_le_of_coeff_eq_one m (appellRow_natDegree_le m c)
  simp [appellRow_coeff_eq,hc]

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



theorem appellCoefficients_zero (p : Polynomial ℂ) (hp : p.Monic) :
    appellCoefficients p 0=1 := by
  simpa [appellCoefficients] using hp.leadingCoeff

theorem appellRow_coefficients (p : Polynomial ℂ) :
    appellRow p.natDegree (appellCoefficients p)=p := by
  ext k
  rw [appellRow_coeff_eq]
  by_cases hk : k ≤ p.natDegree
  · have hn : (p.natDegree.choose k:ℂ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hk
    unfold appellCoefficients
    rw [Nat.sub_sub_self hk,Nat.choose_symm hk]
    field_simp
  · rw [Nat.choose_eq_zero_of_lt (by omega),Nat.cast_zero,zero_mul]
    exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm



end DerivativeChainContinuation



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
open Polynomial DerivativeChainContinuation
namespace DerivativeChainPhaseLock
noncomputable section



theorem multiset_newton_identity (s : Multiset ℂ) (k : ℕ) (hk : 0 < k) :
    multisetPowerSum s k = (-1)^(k+1)*(k:ℂ)*s.esymm k-
      ∑ a ∈ Finset.HasAntidiagonal.antidiagonal k with a.1 ∈ Set.Ioo 0 k,
        (-1)^a.1*s.esymm a.1*multisetPowerSum s a.2 := by
  classical
  have hpowers (q : ℕ) :
      MvPolynomial.aeval (fun x : s => (x:ℂ)) (MvPolynomial.psum s ℂ q)=multisetPowerSum s q := by
    simp only [MvPolynomial.psum,map_sum,map_pow,MvPolynomial.aeval_X]
    exact congrArg Multiset.sum (Multiset.map_univ s (fun z : ℂ => z^q))
  have hesymm (q : ℕ) :
      MvPolynomial.aeval (fun x : s => (x:ℂ)) (MvPolynomial.esymm s ℂ q)=s.esymm q := by
    rw [MvPolynomial.aeval_esymm_eq_multiset_esymm,Multiset.map_univ_coe]
  have h := congrArg (MvPolynomial.aeval (fun x : s => (x:ℂ)))
    (MvPolynomial.psum_eq_mul_esymm_sub_sum s ℂ k hk)
  simpa only [map_sub,map_mul,map_pow,map_neg,map_one,map_natCast,map_sum,hpowers,hesymm] using h

theorem odd_newton_reduction (s : Multiset ℂ) (k : ℕ) (hk : Odd k)
    (hzero : ∀ j<k, Odd j → s.esymm j=0) :
    multisetPowerSum s k=(k:ℂ)*s.esymm k := by
  classical
  revert hk hzero
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk hzero
    have hk0 : 0 < k := hk.pos
    rw [multiset_newton_identity s k hk0,hk.add_one.neg_one_pow,one_mul]
    have hs : (∑ a ∈ Finset.HasAntidiagonal.antidiagonal k with a.1 ∈ Set.Ioo 0 k,
        (-1:ℂ)^a.1*s.esymm a.1*multisetPowerSum s a.2)=0 := by
      apply Finset.sum_eq_zero
      intro a ha
      have hmem := Finset.mem_filter.mp ha
      have hadd := Finset.HasAntidiagonal.mem_antidiagonal.mp hmem.1
      have hapos : 0 < a.1 := hmem.2.1
      have halt : a.1 < k := hmem.2.2
      rcases Nat.even_or_odd a.1 with he | ho
      · have hbodd : Odd a.2 := by
          have hh := Nat.Odd.sub_even (show a.1 ≤ k by omega) hk he
          simpa only [show k-a.1=a.2 by omega] using hh
        have hblt : a.2 < k := by omega
        have hps : multisetPowerSum s a.2=0 := by
          rw [ih a.2 hblt hbodd (by
            intro j hj hodd
            exact hzero j (by omega) hodd),hzero a.2 hblt hbodd,mul_zero]
        rw [hps,mul_zero]
      · rw [hzero a.1 halt ho,mul_zero,zero_mul]
    rw [hs,sub_zero]

theorem appell_odd_esymm (m j : ℕ) (c : ℕ → ℂ) (hc : c 0=1)
    (hj : Odd j) (hjm : j ≤ m) :
    (appellRow m c).roots.esymm j=-(m.choose j:ℂ)*c j := by
  have hp := appellRow_monic m c hc
  have hd := appellRow_natDegree m c hc
  have h := Polynomial.coeff_eq_esymm_roots_of_splits (IsAlgClosed.splits (appellRow m c))
    (k:=m-j) (by rw [hd]; exact Nat.sub_le m j)
  rw [hp.leadingCoeff,one_mul,hd,show m-(m-j)=j by omega,hj.neg_one_pow] at h
  rw [appellRow_coeff_eq,show m-(m-j)=j by omega,Nat.choose_symm hjm] at h
  linear_combination h

theorem appell_odd_moment (m q : ℕ) (c : ℕ → ℂ) (hc : c 0=1)
    (hq : Odd q) (hqm : q ≤ m) (hzero : ∀ j<q, Odd j → c j=0) :
    multisetPowerSum (appellRow m c).roots q=-(q:ℂ)*(m.choose q:ℂ)*c q := by
  have hz : ∀ j<q, Odd j → (appellRow m c).roots.esymm j=0 := by
    intro j hj hjodd
    rw [appell_odd_esymm m j c hc hjodd (by omega),hzero j hj hjodd,mul_zero]
  rw [odd_newton_reduction _ q hq hz,appell_odd_esymm m q c hc hq hqm]
  ring

theorem actual_appell_row_roots (N m : ℕ) (c : ℕ → ℂ) (hm : m ≤ N) :
    ((derivative^[N-m]) (appellRow N c)).roots=(appellRow m c).roots := by
  have h := appellRow_iterate_derivative m (N-m) c
  rw [Nat.add_sub_of_le hm] at h
  rw [h,roots_C_mul]
  exact_mod_cast (Nat.ne_of_gt (Nat.descFactorial_pos.mpr (Nat.sub_le N m)))

theorem actual_appell_odd_moment (N m q : ℕ) (c : ℕ → ℂ) (hc : c 0=1)
    (hq : Odd q) (hqm : q ≤ m) (hmN : m ≤ N)
    (hzero : ∀ j<q, Odd j → c j=0) :
    multisetPowerSum ((derivative^[N-m]) (appellRow N c)).roots q=
      -(q:ℂ)*(m.choose q:ℂ)*c q := by
  rw [actual_appell_row_roots N m c hmN]
  exact appell_odd_moment m q c hc hq hqm hzero

theorem actual_polynomial_odd_moment (p : Polynomial ℂ) (hp : p.Monic)
    (m q : ℕ) (hq : Odd q) (hqm : q ≤ m) (hm : m ≤ p.natDegree)
    (hzero : ∀ j<q, Odd j → appellCoefficients p j=0) :
    multisetPowerSum ((derivative^[p.natDegree-m]) p).roots q=
      -(q:ℂ)*(m.choose q:ℂ)*appellCoefficients p q := by
  have h := actual_appell_odd_moment p.natDegree m q (appellCoefficients p)
    (appellCoefficients_zero p hp) hq hqm hm hzero
  simpa only [appellRow_coefficients] using h

end
end DerivativeChainPhaseLock



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Polynomial DerivativeChainContinuation
namespace DerivativeChainPhaseLock
noncomputable section

theorem clusterErrorBudget_nonneg (A B Z : Multiset ℂ) (q : ℕ) (ε ρ : ℝ)
    (hε : 0 ≤ ε) (hρ : 0 ≤ ρ) : 0 ≤ clusterErrorBudget A B Z q ε ρ := by
  have heta : 0 ≤ (1+ε)^q-1 := sub_nonneg.mpr (one_le_pow₀ (by linarith : 1 ≤ 1+ε))
  exact add_nonneg (mul_nonneg (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) heta)
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hρ _))

theorem count_balance_of_zero_moment (q : ℕ) (a : ℂ) (δ E : ℝ)
    (herror : ‖(δ:ℂ)*a^q‖ ≤ E*‖a‖^q) : a=0 ∨ |δ| ≤ E := by
  by_cases ha : a=0
  · exact Or.inl ha
  · right
    have hp : 0 < ‖a‖^q := pow_pos (norm_pos_iff.mpr ha) _
    have he : |δ| *‖a‖^q ≤ E*‖a‖^q := by
      simpa only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs] using herror
    exact le_of_mul_le_mul_right he hp

theorem orientation_of_moment_error (q : ℕ) (a : ℂ) (δ E : ℝ)
    (hE : 0 ≤ E) (ha : a ≠ 0) (hδ : E < |δ|) (S : ℂ)
    (herror : ‖S-(δ:ℂ)*a^q‖ ≤ E*‖a‖^q) :
    0 < (S*star ((δ:ℂ)*a^q)).re ∧
      |(S/((δ:ℂ)*a^q)).arg| ≤ Real.arcsin (E/|δ|) := by
  have hδpos : 0 < |δ| := hE.trans_lt hδ
  have hp : 0 < ‖a‖^q := pow_pos (norm_pos_iff.mpr ha) _
  have hb : (δ:ℂ)*a^q ≠ 0 := mul_ne_zero
    (Complex.ofReal_ne_zero.mpr (abs_pos.mp hδpos)) (pow_ne_zero _ ha)
  have hbnorm : ‖(δ:ℂ)*a^q‖=|δ| *‖a‖^q := by
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
  have hratio : ‖S/((δ:ℂ)*a^q)-1‖ ≤ E/|δ| := by
    have he : S/((δ:ℂ)*a^q)-1=(S-(δ:ℂ)*a^q)/((δ:ℂ)*a^q) := by
      rw [sub_div,div_self hb]
    rw [he,norm_div,hbnorm]
    calc
      _ ≤ (E*‖a‖^q)/(|δ| *‖a‖^q) :=
        div_le_div_of_nonneg_right herror (mul_nonneg (abs_nonneg _) (pow_nonneg (norm_nonneg _) _))
      _ = E/|δ| := by field_simp [ne_of_gt hδpos,ne_of_gt hp]
  have hphase := disk_phase_control (S/((δ:ℂ)*a^q)) (E/|δ|)
    (div_nonneg hE (abs_nonneg _)) ((div_lt_one hδpos).mpr hδ) hratio
  refine ⟨?_,hphase.2⟩
  have h := hphase.1
  rw [Complex.div_re,← add_div] at h
  have hn := (div_pos_iff_of_pos_right (Complex.normSq_pos.mpr hb)).mp h
  simpa only [Complex.mul_re,Complex.star_def,Complex.conj_re,Complex.conj_im,mul_neg,sub_neg_eq_add] using hn





end
end DerivativeChainPhaseLock



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Polynomial DerivativeChainContinuation
open DerivativeChainPhaseLock








theorem solution (p : Polynomial ℂ) (hp : p.Monic)
    (m q : ℕ) (hq : Odd q) (hqm : q ≤ m) (hm : m ≤ p.natDegree)
    (hzero : ∀ j<q, Odd j → _root_.DerivativeChainContinuation.appellCoefficients p j=0)
    (A B Z : Multiset ℂ)
    (hpartition : ((derivative^[p.natDegree-m]) p).roots=A+B+Z)
    (a : ℂ) (ε ρ : ℝ) (hε : 0 ≤ ε) (hρ : 0 ≤ ρ)
    (hA : ∀ z∈A, ‖z-a‖ ≤ ε*‖a‖)
    (hB : ∀ z∈B, ‖z+a‖ ≤ ε*‖a‖)
    (hZ : ∀ z∈Z, ‖z‖ ≤ ρ*‖a‖) :
    let S := _root_.DerivativeChainPhaseLock.multisetPowerSum ((derivative^[p.natDegree-m]) p).roots q;
    let δ := _root_.DerivativeChainPhaseLock.clusterImbalance A B;
    let E := _root_.DerivativeChainPhaseLock.clusterErrorBudget A B Z q ε ρ;
    S=-(q:ℂ)*(m.choose q:ℂ)*_root_.DerivativeChainContinuation.appellCoefficients p q ∧
      (a=0 → _root_.DerivativeChainContinuation.appellCoefficients p q=0) ∧
      (_root_.DerivativeChainContinuation.appellCoefficients p q=0 → a=0 ∨ |δ| ≤ E) ∧
      (a ≠ 0 → E < |δ| → 0 < (S*star ((δ:ℂ)*a^q)).re ∧
        |(S/((δ:ℂ)*a^q)).arg| ≤ Real.arcsin (E/|δ|)) := by
  let S := _root_.DerivativeChainPhaseLock.multisetPowerSum ((derivative^[p.natDegree-m]) p).roots q
  let δ := _root_.DerivativeChainPhaseLock.clusterImbalance A B
  let E := _root_.DerivativeChainPhaseLock.clusterErrorBudget A B Z q ε ρ
  have hmoment : S=-(q:ℂ)*(m.choose q:ℂ)*_root_.DerivativeChainContinuation.appellCoefficients p q :=
    _root_.DerivativeChainPhaseLock.actual_polynomial_odd_moment p hp m q hq hqm hm hzero
  have herr : ‖S-(δ:ℂ)*a^q‖ ≤ E*‖a‖^q := by
    dsimp only [S,δ,E]
    rw [hpartition]
    exact _root_.DerivativeChainPhaseLock.cluster_moment_error A B Z q hq a ε ρ hε hρ hA hB hZ
  have hE : 0 ≤ E := _root_.DerivativeChainPhaseLock.clusterErrorBudget_nonneg A B Z q ε ρ hε hρ
  have hfac : -(q:ℂ)*(m.choose q:ℂ) ≠ 0 := mul_ne_zero
    (neg_ne_zero.mpr (by exact_mod_cast Nat.ne_of_gt hq.pos))
    (by exact_mod_cast Nat.choose_ne_zero hqm)
  refine ⟨hmoment,?_,?_,?_⟩
  · intro ha
    have hn : ‖S‖ ≤ 0 := by
      simpa only [ha,zero_pow (Nat.ne_of_gt hq.pos),mul_zero,norm_zero,sub_zero] using herr
    have hzS : S=0 := norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))
    have he : (-(q:ℂ)*(m.choose q:ℂ))*_root_.DerivativeChainContinuation.appellCoefficients p q=0 := by rw [← hmoment,hzS]
    exact (mul_eq_zero.mp he).resolve_left hfac
  · intro hc
    have hzS : S=0 := by rw [hmoment,hc,mul_zero]
    have he : ‖(δ:ℂ)*a^q‖ ≤ E*‖a‖^q := by simpa only [hzS,zero_sub,norm_neg] using herr
    exact _root_.DerivativeChainPhaseLock.count_balance_of_zero_moment q a δ E he
  · intro ha hδ
    exact _root_.DerivativeChainPhaseLock.orientation_of_moment_error q a δ E hE ha hδ S herr
