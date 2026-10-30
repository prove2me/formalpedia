-- Prove2me | solution 1 for CubicTurning.unit_disk_cubic_constant_sharp
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:01:45.773036+00:00
-- url     : https://prove2.me/submissions/cdeba43a-edc3-4cf7-ad13-70b5beea6d29

import Mathlib
import Definitions.Def_CubicTurning_finite_balanced
import Definitions.Def_CubicTurning_foundations
import Definitions.Def_CubicTurning_unit_disk
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_CubicTurning_energy_eq_halfAngleEnergy
import Theorems.Thm_CubicTurning_no_smaller_nonnegative_balanced_constant
import Theorems.Thm_CubicTurning_sharp_finite_balanced_law_lower
import Theorems.Thm_CubicTurning_unit_disk_law_double
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate


set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate
namespace CubicTurning













































theorem variance_decomposition (r : ℝ) (a b c : ℂ)
    (hsecond : a^2+b^2+c^2=6*(r:ℂ)^2) :
    variance a b c = 2*r^2+(2/3)*(a.im^2+b.im^2+c.im^2) := by
  have h := congrArg Complex.re hsecond
  simp [pow_two,Complex.mul_re] at h
  unfold variance
  rw [←Complex.normSq_eq_norm_sq,←Complex.normSq_eq_norm_sq,←Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply]
  nlinarith
































































end CubicTurning


set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate
namespace CubicTurning












theorem sharp_family_center (t : ℝ) :
    sharpCentral t+sharpOuterPlus t+sharpOuterMinus t=0 := by
  apply Complex.ext <;> simp [sharpCentral,sharpOuterPlus,sharpOuterMinus] <;> ring

theorem sharp_family_second (t : ℝ) :
    (sharpCentral t)^2+(sharpOuterPlus t)^2+(sharpOuterMinus t)^2=6 := by
  have hs : (Real.sqrt (3+3*t^2/4))^2=3+3*t^2/4 := Real.sq_sqrt (by positivity)
  simp only [pow_two] at hs
  apply Complex.ext <;> simp [sharpCentral,sharpOuterPlus,sharpOuterMinus,pow_two,
    Complex.mul_re,Complex.mul_im] <;> nlinarith [hs]

theorem sharp_family_variance (t : ℝ) :
    variance (sharpCentral t) (sharpOuterPlus t) (sharpOuterMinus t)=2+t^2 := by
  have hv := variance_decomposition 1 (sharpCentral t) (sharpOuterPlus t) (sharpOuterMinus t)
    (by simpa using sharp_family_second t)
  convert hv using 1 <;> simp [sharpCentral,sharpOuterPlus,sharpOuterMinus] <;> ring

























theorem no_smaller_balanced_constant (K : ℝ) (hK : K<2/3) :
    ∃ t : ℝ, 0<t ∧ t≤1 ∧
      ∀ (n : ℕ) (L : FiniteBalancedForwardLaw n (sharpCentral t) (sharpOuterPlus t) (sharpOuterMinus t)),
        K*variance (sharpCentral t) (sharpOuterPlus t) (sharpOuterMinus t)<L.meanEnergy := by
  by_cases hK₀ : 0≤K
  · exact no_smaller_nonnegative_balanced_constant K hK₀ hK
  · refine ⟨1,by norm_num,by norm_num,?_⟩
    intro n L
    have hlo := sharp_finite_balanced_law_lower 1 (by norm_num) (by norm_num) L
    have hKn : K<0 := lt_of_not_ge hK₀
    have hpos : 0<L.meanEnergy := lt_of_lt_of_le (by positivity) hlo
    have hk : K*(2+(1:ℝ)^2)<0 := mul_neg_of_neg_of_pos hKn (by norm_num)
    rw [sharp_family_variance]
    exact hk.trans hpos

theorem balanced_meanEnergy_eq_half_angle {n : ℕ} {a b c : ℂ}
    (L : FiniteBalancedForwardLaw n a b c) :
    L.meanEnergy=∑ i,L.weights i*halfAngleEnergy (L.axes i)
      (L.paths i 1-L.paths i 0) (L.paths i 2-L.paths i 1) := by
  unfold FiniteBalancedForwardLaw.meanEnergy
  apply Finset.sum_congr rfl
  intro i _
  rw [energy_eq_halfAngleEnergy _ _ _ (L.forward i)]




















end CubicTurning


set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate
namespace CubicTurning









theorem variance_positive_scale (s : ℝ) (hs : 0<s) (a b c : ℂ) :
    variance ((s:ℂ)*a) ((s:ℂ)*b) ((s:ℂ)*c)=s^2*variance a b c := by
  simp [variance,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hs]
  ring





theorem unit_disk_sharp_roots (t : ℝ) (ht : 0<t) (ht1 : t≤1) :
    ‖unitDiskCentral t‖≤1 ∧ ‖unitDiskOuterPlus t‖≤1 ∧ ‖unitDiskOuterMinus t‖≤1 := by
  have htsq : t^2≤1 := by nlinarith [mul_nonneg (show 0≤1-t by linarith) (show 0≤1+t by linarith)]
  have hsqrt : (Real.sqrt (3+3*t^2/4))^2=3+3*t^2/4 := Real.sq_sqrt (by positivity)
  have hc : ‖sharpCentral t‖≤2 := by
    simp [sharpCentral,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht]
    linarith
  have hb : ‖sharpOuterPlus t‖≤2 := by
    have hn : ‖sharpOuterPlus t‖^2=3+t^2 := by
      rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply]
      dsimp only [sharpOuterPlus]
      nlinarith [hsqrt]
    nlinarith [norm_nonneg (sharpOuterPlus t)]
  have hd : ‖sharpOuterMinus t‖≤2 := by
    have hn : ‖sharpOuterMinus t‖^2=3+t^2 := by
      rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply]
      dsimp only [sharpOuterMinus]
      nlinarith [hsqrt]
    nlinarith [norm_nonneg (sharpOuterMinus t)]
  simp only [unitDiskCentral,unitDiskOuterPlus,unitDiskOuterMinus,norm_mul]
  norm_num
  exact ⟨by linarith,by linarith,by linarith⟩

theorem unit_disk_center (t : ℝ) :
    unitDiskCentral t+unitDiskOuterPlus t+unitDiskOuterMinus t=0 := by
  dsimp [unitDiskCentral,unitDiskOuterPlus,unitDiskOuterMinus]
  linear_combination (sharp_family_center t)/2

theorem unit_disk_variance (t : ℝ) :
    variance (unitDiskCentral t) (unitDiskOuterPlus t) (unitDiskOuterMinus t)=
      (1/4)*variance (sharpCentral t) (sharpOuterPlus t) (sharpOuterMinus t) := by
  have h:=variance_positive_scale (1/2) (by norm_num) (sharpCentral t) (sharpOuterPlus t) (sharpOuterMinus t)
  norm_num [unitDiskCentral,unitDiskOuterPlus,unitDiskOuterMinus] at h ⊢
  exact h



theorem no_smaller_unit_disk_signed_turning_constant (K : ℝ) (hK : K<2/3) :
    ∃ t : ℝ, 0<t ∧ t≤1 ∧
      ‖unitDiskCentral t‖≤1 ∧ ‖unitDiskOuterPlus t‖≤1 ∧ ‖unitDiskOuterMinus t‖≤1 ∧
      (unitDiskCentral t+unitDiskOuterPlus t+unitDiskOuterMinus t=0) ∧
      ∀ (n : ℕ) (L : FiniteBalancedForwardLaw n (unitDiskCentral t) (unitDiskOuterPlus t) (unitDiskOuterMinus t)),
        K*variance (unitDiskCentral t) (unitDiskOuterPlus t) (unitDiskOuterMinus t)<
          ∑ i,L.weights i*halfAngleEnergy (L.axes i)
            (L.paths i 1-L.paths i 0) (L.paths i 2-L.paths i 1) := by
  obtain ⟨t,ht,ht1,hbound⟩:=no_smaller_balanced_constant K hK
  obtain ⟨hc,hb,hd⟩:=unit_disk_sharp_roots t ht ht1
  refine ⟨t,ht,ht1,hc,hb,hd,unit_disk_center t,?_⟩
  intro n L
  obtain ⟨M,hM⟩:=unit_disk_law_double t L
  have h:=hbound n M
  rw [hM] at h
  rw [←balanced_meanEnergy_eq_half_angle L,unit_disk_variance]
  linarith

theorem unit_disk_source_polynomial (t : ℝ) (ht : 0<t) (ht1 : t≤1) :
    let p:=DerivativeChainPrivate.fromRoots
      (![unitDiskCentral t,unitDiskOuterPlus t,unitDiskOuterMinus t] : Fin 3 → ℂ)
    p.Monic ∧ p.natDegree=3 ∧ ∀ z : ℂ, p.eval z=0 → ‖z‖≤1 := by
  dsimp only
  let a:=unitDiskCentral t
  let b:=unitDiskOuterPlus t
  let c:=unitDiskOuterMinus t
  have hpoly : DerivativeChainPrivate.fromRoots (![a,b,c] : Fin 3 → ℂ)=
      (Polynomial.X-Polynomial.C a)*((Polynomial.X-Polynomial.C b)*(Polynomial.X-Polynomial.C c)) := by
    simp [DerivativeChainPrivate.fromRoots,Fin.prod_univ_succ]
  have ha:=(Polynomial.monic_X_sub_C a)
  have hb:=(Polynomial.monic_X_sub_C b)
  have hc:=(Polynomial.monic_X_sub_C c)
  change (DerivativeChainPrivate.fromRoots (![a,b,c] : Fin 3 → ℂ)).Monic ∧ _
  refine ⟨?_,?_,?_⟩
  · rw [hpoly]
    exact ha.mul (hb.mul hc)
  · rw [hpoly,ha.natDegree_mul (hb.mul hc),hb.natDegree_mul hc]
    simp
  · intro z hz
    rw [hpoly] at hz
    simp only [Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C] at hz
    have hroot : z=a ∨ z=b ∨ z=c := by simpa only [mul_eq_zero,sub_eq_zero,or_assoc] using hz
    obtain ⟨h₀,h₁,h₂⟩:=unit_disk_sharp_roots t ht ht1
    rcases hroot with rfl|rfl|rfl
    · exact h₀
    · exact h₁
    · exact h₂








end CubicTurning

open CubicTurning in
theorem solution (K : ℝ) (hK : K<2/3) :
    ∃ (p : Polynomial ℂ) (a b c : ℂ),
      p=DerivativeChainPrivate.fromRoots (![a,b,c] : Fin 3 → ℂ) ∧
      p.Monic ∧ p.natDegree=3 ∧ (∀ z : ℂ,p.eval z=0 → ‖z‖≤1) ∧
      a+b+c=0 ∧
      ∀ (n : ℕ) (L : FiniteBalancedForwardLaw n a b c),
        K*variance a b c < ∑ i,L.weights i*halfAngleEnergy (L.axes i)
          (L.paths i 1-L.paths i 0) (L.paths i 2-L.paths i 1) := by
  obtain ⟨t,ht,ht1,h₀,h₁,h₂,hcenter,hbound⟩:=no_smaller_unit_disk_signed_turning_constant K hK
  obtain ⟨hmonic,hdegree,hdisk⟩:=unit_disk_source_polynomial t ht ht1
  refine ⟨_,unitDiskCentral t,unitDiskOuterPlus t,unitDiskOuterMinus t,rfl,hmonic,hdegree,hdisk,hcenter,hbound⟩
