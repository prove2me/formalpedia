-- Prove2me | solution 1 for DerivativeChainContinuation.positive_activation_parameter_formula
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T00:19:20.252012+00:00
-- url     : https://prove2.me/submissions/e3914c65-8ffb-4c58-8d1e-1ffb4949d8e1

import Mathlib
import Definitions.Def_DerivativeChainContinuation_PositiveSpokeClosure
import Definitions.Def_DerivativeChainPrivate_SpokeRows
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_positive_spoke_activation_row
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators









theorem positive_linear_quotient_single_root (V : Polynomial ℝ)
    (hV : PositiveQuotient V) (hdegree : V.natDegree=1) :
    ∃ b : ℝ,0<b ∧ V.eval b=0 ∧ ∀ t : ℝ,V.eval t=0 → t=b := by
  have hc : V.roots.card=1 := by rw [←hV.2.1.natDegree_eq_card_roots,hdegree]
  obtain ⟨b,hb⟩ := Multiset.card_eq_one.mp hc
  have hmem : b∈V.roots := by rw [hb]; simp
  refine ⟨b,hV.2.2 b hmem,(mem_roots hV.1).mp hmem,?_⟩
  intro t ht
  have htm := (mem_roots hV.1).mpr ht
  rw [hb] at htm
  simpa using htm







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
























end DerivativeChainContinuation


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators























theorem spoke_coefficient_multiple (k r j : ℕ) (Q : Polynomial ℝ) (hk : 1 ≤ k) :
    (spokePoly k r Q).coeff (r+k*j)=(Q.coeff j : ℂ) := by
  rw [spokePoly,show r+k*j=k*j+r by omega,coeff_X_pow_mul,←expand_eq_comp_X_pow,
    coeff_expand_mul' (show 0<k by omega),coeff_map]
  rfl

theorem spoke_top_mode_coefficients (k r : ℕ) (Q : Polynomial ℝ)
    (hk : 1 ≤ k) (hQdegree : 0<Q.natDegree) :
    (spokePoly k r Q).coeff (r+k*Q.natDegree)=(Q.leadingCoeff : ℂ) ∧
      (spokePoly k r Q).coeff (r+k*Q.natDegree-k)=(Q.nextCoeff : ℂ) := by
  constructor
  · rw [spoke_coefficient_multiple k r Q.natDegree Q hk,coeff_natDegree]
  · have hindex : r+k*Q.natDegree-k=r+k*(Q.natDegree-1) := by
      have he : Q.natDegree=(Q.natDegree-1)+1 := by omega
      nth_rw 1 [he]
      rw [Nat.mul_add,Nat.mul_one]
      omega
    rw [hindex,spoke_coefficient_multiple k r (Q.natDegree-1) Q hk,
      ←nextCoeff_of_natDegree_pos hQdegree]
















end DerivativeChainContinuation



set_option autoImplicit false

namespace DerivativeChainPrivate
open Polynomial







theorem spoke_natDegree (k r : ℕ) (q : Polynomial ℝ) (hq : q ≠ 0) (hk : 0 < k) :
    (spokePoly k r q).natDegree = r + k * q.natDegree := by
  have hmap : q.map Complex.ofRealHom ≠ 0 := Polynomial.map_ne_zero hq
  have hcomp : (q.map Complex.ofRealHom).comp (X ^ k) ≠ 0 := by
    rw [ne_eq, Polynomial.comp_eq_zero_iff]
    simp only [hmap, false_or]
    intro h
    have hdegree := congrArg Polynomial.natDegree h.2
    simp only [natDegree_X_pow, natDegree_C] at hdegree
    omega
  rw [spokePoly, natDegree_mul (pow_ne_zero _ X_ne_zero) hcomp,
    natDegree_X_pow, natDegree_comp, natDegree_map, natDegree_X_pow]
  ring



theorem spoke_eval_real_power (k r : ℕ) (q : Polynomial ℝ) (w : ℂ) (y : ℝ)
    (hw : w ^ k = (y : ℂ)) :
    (spokePoly k r q).eval w = w ^ r * ((q.eval y : ℝ) : ℂ) := by
  simp only [spokePoly, eval_mul, eval_pow, eval_X, eval_comp, hw]
  exact congrArg (fun z : ℂ => w ^ r * z)
    (Polynomial.eval_map_apply (f := Complex.ofRealHom) (p := q) y)



theorem spoke_root_power_real (k r : ℕ) (q : Polynomial ℝ) (hq : q.Splits)
    (hqne : q ≠ 0) (w : ℂ) (hw : w ≠ 0) (hz : (spokePoly k r q).eval w = 0) :
    ∃ y : ℝ, w ^ k = (y : ℂ) := by
  have heval : (q.map Complex.ofRealHom).eval (w ^ k) = 0 := by
    simp only [spokePoly, eval_mul, eval_pow, eval_X, eval_comp] at hz
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hw)
  obtain ⟨y, hy⟩ := hq.mem_range_of_isRoot hqne heval
  exact ⟨y, hy.symm⟩

end DerivativeChainPrivate


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators



theorem positiveQuotient_eval_ne_of_nonpos (Q : Polynomial ℝ) (hQ : PositiveQuotient Q)
    (x : ℝ) (hx : x≤0) : Q.eval x≠0 := by
  intro h
  have hp := hQ.2.2 x ((mem_roots hQ.1).mpr h)
  linarith













theorem positive_spoke_nonzero_root_power (k r : ℕ) (Q : Polynomial ℝ)
    (hQ : PositiveQuotient Q) (z : ℂ) (hz : z≠0)
    (hroot : (spokePoly k r Q).eval z=0) :
    ∃ t : ℝ,0<t ∧ z^k=(t : ℂ) ∧ Q.eval t=0 := by
  obtain ⟨t,ht⟩ := spoke_root_power_real k r Q hQ.2.1 hQ.1 z hz hroot
  have hv : Q.eval t=0 := by
    rw [spoke_eval_real_power k r Q z t ht] at hroot
    have h := (mul_eq_zero.mp hroot).resolve_left (pow_ne_zero _ hz)
    exact Complex.ofReal_eq_zero.mp h
  exact ⟨t,hQ.2.2 t ((mem_roots hQ.1).mpr hv),ht,hv⟩






end DerivativeChainContinuation

theorem solution (n : ℕ) (a : Fin (n+1) → ℂ)
    (k r : ℕ) (Q : Polynomial ℝ) (hk : 2 ≤ k) (hQ : PositiveQuotient Q)
    (hQdegree : 0<Q.natDegree) (hp : fromRoots a=spokePoly k r Q) :
    0<Q.roots.sum/(Nat.choose (n+1) k : ℝ) ∧
      ∀ z : ℂ,(row a k).eval z=0 ↔ z^k=((Q.roots.sum/(Nat.choose (n+1) k : ℝ) : ℝ) : ℂ) := by
  have hdegree : (spokePoly k r Q).natDegree=n+1 := by rw [←hp,actual_complex_source_natDegree]
  have hN : r+k*Q.natDegree=n+1 := by rw [←spoke_natDegree k r Q hQ.1 (by omega)]; exact hdegree
  have hkl : k ≤ n+1 := by
    have hm : k ≤ k*Q.natDegree := Nat.le_mul_of_pos_right k hQdegree
    omega
  obtain ⟨V,hV,hVdegree,hrow⟩ := positive_spoke_activation_row n k r Q hk hQ hQdegree hdegree
  obtain ⟨b,hb,hVroot,hVunique⟩ := positive_linear_quotient_single_root V hV hVdegree
  have hlinear : V.coeff 0+b*V.coeff 1=0 := by
    rw [eq_X_add_C_of_natDegree_le_one hVdegree.le] at hVroot
    simp only [eval_add,eval_mul,eval_C,eval_X] at hVroot
    nlinarith
  obtain ⟨htop,hnext⟩ := spoke_top_mode_coefficients k r Q (by omega) hQdegree
  rw [hN] at htop hnext
  have hVcoeff0 : (spokePoly k 0 V).coeff 0=(V.coeff 0 : ℂ) := by
    simpa only [Nat.mul_zero,Nat.zero_add] using spoke_coefficient_multiple k 0 0 V (by omega)
  have hzeroComplex := congrArg (fun p : Polynomial ℂ => p.coeff 0) hrow
  rw [coeff_iterate_derivative,zero_add,nsmul_eq_mul,hVcoeff0,Nat.descFactorial_self,hnext] at hzeroComplex
  have hzero : ((n+1-k).factorial : ℝ)*Q.nextCoeff=V.coeff 0 := by exact_mod_cast hzeroComplex
  have htopComplex := congrArg (fun p : Polynomial ℂ => p.coeff k) hrow
  rw [coeff_iterate_derivative,nsmul_eq_mul,show k+(n+1-k)=n+1 by omega,htop] at htopComplex
  have hVcoeff : (spokePoly k 0 V).coeff k=(V.coeff 1 : ℂ) := by
    simpa only [mul_one,zero_add] using spoke_coefficient_multiple k 0 1 V (by omega)
  rw [hVcoeff] at htopComplex
  have htopReal : ((n+1).descFactorial (n+1-k) : ℝ)*Q.leadingCoeff=V.coeff 1 := by
    exact_mod_cast htopComplex
  have hdesc : ((n+1).descFactorial (n+1-k) : ℝ)=
      ((n+1-k).factorial : ℝ)*(Nat.choose (n+1) k : ℝ) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose,Nat.choose_symm hkl,Nat.cast_mul]
  rw [hdesc] at htopReal
  have hnextCoeff := hQ.2.1.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
  rw [hnextCoeff] at hzero
  have hprod : ((n+1-k).factorial : ℝ)*Q.leadingCoeff*
      ((Nat.choose (n+1) k : ℝ)*b-Q.roots.sum)=0 := by
    rw [←hzero,←htopReal] at hlinear
    linear_combination hlinear
  have hfacne : ((n+1-k).factorial : ℝ)*Q.leadingCoeff≠0 := mul_ne_zero
    (by exact_mod_cast (Nat.factorial_ne_zero (n+1-k))) (leadingCoeff_ne_zero.mpr hQ.1)
  have heq := (mul_eq_zero.mp hprod).resolve_left hfacne
  have hchoose : (Nat.choose (n+1) k : ℝ)≠0 := by
    exact_mod_cast (ne_of_gt (Nat.choose_pos hkl))
  have hbvalue : b=Q.roots.sum/(Nat.choose (n+1) k : ℝ) := by
    apply (eq_div_iff hchoose).mpr
    linarith
  refine ⟨by rwa [←hbvalue],?_⟩
  intro z
  have hrowActual : row a k=spokePoly k 0 V := by simpa only [row,hp] using hrow
  rw [hrowActual]
  constructor
  · intro hz
    have hz0 : z≠0 := by
      intro he
      subst z
      rw [spoke_eval_real_power k 0 V 0 0 (by simp [show k≠0 by omega]),pow_zero,one_mul] at hz
      exact (positiveQuotient_eval_ne_of_nonpos V hV 0 le_rfl) (Complex.ofReal_eq_zero.mp hz)
    obtain ⟨t,ht,hpow,hroot⟩ := positive_spoke_nonzero_root_power k 0 V hV z hz0 hz
    rw [hVunique t hroot,hbvalue] at hpow
    exact hpow
  · intro hz
    rw [←hbvalue] at hz
    rw [spoke_eval_real_power k 0 V z b hz,hVroot]
    simp
