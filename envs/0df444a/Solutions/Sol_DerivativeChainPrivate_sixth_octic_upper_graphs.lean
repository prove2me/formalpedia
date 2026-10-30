-- Prove2me | solution 1 for DerivativeChainPrivate.sixth_octic_upper_graphs
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T01:36:44.066774+00:00
-- url     : https://prove2.me/submissions/9d35a425-983f-4a8c-aaa2-aa418f52a7bc

import Mathlib
import Definitions.Def_DerivativeChainPrivate_SixthOcticAlgebra
import Definitions.Def_DerivativeChainPrivate_SixthOcticErrorDerivative
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPrivate_sixth_octic_inverse_exact
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
open Polynomial DerivativeChainPrivate MeasureTheory Set Filter
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped Topology BigOperators


set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace DerivativeChainPrivate











theorem sixth_octic_pole_bound (u : ℂ) (hu : ‖u‖≤3/10) :
    1-(17/33:ℂ)*u≠0 ∧ ‖(1-(17/33:ℂ)*u)⁻¹‖≤6/5 := by
  have hn:=norm_sub_norm_le (1:ℂ) ((17/33:ℂ)*u)
  norm_num [norm_mul] at hn
  have hl : (5/6:ℝ)≤‖1-(17/33:ℂ)*u‖ := by linarith
  refine ⟨norm_pos_iff.mp (by linarith),?_⟩
  rw [norm_inv]
  have hi:=inv_anti₀ (by norm_num : (0:ℝ)<5/6) hl
  norm_num at hi
  exact hi
end DerivativeChainPrivate

theorem solution (β z : ℂ) (hx : 0<z.re) (hX : 4≤z.re^2)
    (hroot : (5440/13)*β^2*z^2-(92480/429)*β^2-56*β*z^5+(680/3)*β*z^3-(5780/39)*β*z+
      z^8-(28/3)*z^6+(595/24)*z^4-(1445/78)*z^2+24565/13728=0) :
    β/z=(((91-3*Real.sqrt 429)/1360:ℝ):ℂ)*z^2-
      ((13/55-27*Real.sqrt 429/4840:ℝ):ℂ)+sixthOcticRemainder z/z ∨
    β/z=(((91+3*Real.sqrt 429)/1360:ℝ):ℂ)*z^2-
      ((13/55+27*Real.sqrt 429/4840:ℝ):ℂ)+
      ((1071/9680)*z/(z^2-17/33)-sixthOcticRemainder z)/z := by
  have hz : z≠0 := by intro he; simp [he] at hx
  have hnorm : 4≤‖z‖^2 := by rw [Complex.sq_norm,Complex.normSq_apply]; nlinarith [sq_nonneg z.im]
  have hn : ‖z⁻¹‖^2≤1/4 := by
    rw [norm_inv,inv_pow]
    apply (inv_le_comm₀ (by positivity : 0<‖z‖^2) (by norm_num)).mpr
    norm_num
    exact hnorm
  have hu : ‖(z⁻¹)^2‖≤3/10 := by rw [norm_pow]; linarith
  have hpole:=(sixth_octic_pole_bound ((z⁻¹)^2) hu).1
  have hzp : z^2-(17/33:ℂ)≠0 := by
    intro he
    apply hpole
    field_simp
    linear_combination (33:ℂ)*he
  let S:=Complex.sqrt (sixthOcticRadicand ((z⁻¹)^2))
  let s : ℂ:=(Real.sqrt 429:ℂ)
  have hs : s^2=429 := by dsimp [s]; rw [←Complex.ofReal_pow,Real.sq_sqrt (by norm_num)]; norm_num
  have hS : S^2=sixthOcticRadicand ((z⁻¹)^2) := Complex.cpow_nat_inv_pow _ (by norm_num : (2:ℕ)≠0)
  have hd : (β*(z^2-17/33)-z*((91/1360)*z^4-(13/48)*z^2+17/96))^2=
      (3861/1849600)*(z^10-(2210/363)*z^8+(27455/2178)*z^6-(859775/84942)*z^4+
        (2088025/1019304)*z^2+35496425/33637032) := by
    linear_combination (13/5440)*(z^2-17/33)*hroot
  have hsquare : ((3/1360)*s*z^5*S)^2=
      (3861/1849600)*(z^10-(2210/363)*z^8+(27455/2178)*z^6-(859775/84942)*z^4+
        (2088025/1019304)*z^2+35496425/33637032) := by
    calc
      _=(9/1849600)*s^2*z^10*S^2 := by ring
      _=_ := by rw [hs,hS]; unfold sixthOcticRadicand; field_simp <;> ring
  have hsplit:=(sq_eq_sq_iff_eq_or_eq_neg).mp (hd.trans hsquare.symm)
  have hbase : β/z=((91/1360)*z^4-(13/48)*z^2+17/96-(3*s/1360)*z^4*S)/(z^2-17/33) ∨
      β/z=((91/1360)*z^4-(13/48)*z^2+17/96+(3*s/1360)*z^4*S)/(z^2-17/33) := by
    rcases hsplit with hp|hm
    · right
      apply (div_eq_div_iff hz hzp).mpr
      linear_combination hp
    · left
      apply (div_eq_div_iff hz hzp).mpr
      linear_combination hm
  have hminus:=sixth_octic_inverse_exact z hz hn
  have hplus : (((91+3*Real.sqrt 429)/1360:ℝ):ℂ)*z^2-
      ((13/55+27*Real.sqrt 429/4840:ℝ):ℂ)+
      ((1071/9680)*z/(z^2-17/33)-sixthOcticRemainder z)/z=
      ((91/1360)*z^4-(13/48)*z^2+17/96+(3*s/1360)*z^4*S)/(z^2-17/33) := by
    calc
      _=(91/680)*z^2-26/55+(1071/9680)/(z^2-17/33)-
          ((((91-3*Real.sqrt 429)/1360:ℝ):ℂ)*z^2-
            ((13/55-27*Real.sqrt 429/4840:ℝ):ℂ)+sixthOcticRemainder z/z) := by
        push_cast
        field_simp <;> ring
      _=_ := by
        rw [hminus]
        apply (eq_div_iff hzp).mpr
        rw [sub_mul,add_mul,div_mul_cancel₀ _ hzp,div_mul_cancel₀ _ hzp]
        dsimp only [s,S]
        push_cast
        ring
  rcases hbase with hm|hp
  · left
    rw [hminus]
    convert hm using 1 <;> dsimp only [s,S] <;> push_cast <;> ring
  · right
    rw [hplus]
    exact hp
