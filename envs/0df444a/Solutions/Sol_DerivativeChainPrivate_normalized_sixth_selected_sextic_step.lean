-- Prove2me | solution 1 for DerivativeChainPrivate.normalized_sixth_selected_sextic_step
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T05:12:04.722831+00:00
-- url     : https://prove2.me/submissions/b6e1cd91-60ee-4f20-ab3f-fd283e189254

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChainPrivate_higher_power_radicals
import Definitions.Def_TeschlQM_Herglotz_borelTransform
import Theorems.Thm_DerivativeChainPrivate_normalized_sixth_sextic_step
import Theorems.Thm_DerivativeChainPrivate_sixth_sextic_nonnegative_im
import Theorems.Thm_DerivativeChainPrivate_sixth_sextic_radicand_avoids_nonnegative
import Theorems.Thm_DerivativeChainPrivate_sixth_sextic_real_exterior
import Theorems.Thm_DerivativeChainPrivate_sixth_sextic_selected_graph
import Theorems.Thm_DerivativeChainPrivate_sixth_sextic_selected_localization
import Theorems.Thm_TeschlQM_Herglotz_herglotz_representation
import Theorems.Thm_TeschlQM_Herglotz_stieltjes_inversion_formula
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
open MeasureTheory Filter Set
open scoped Topology

theorem measure_Icc_zero_of_real_extension (μ : Measure ℝ) [IsFiniteMeasure μ]
    (a b : ℝ) (hab : a < b) (E : ℂ → ℂ) (hE : Continuous E)
    (hreal : ∀ t : ℝ, (E (t : ℂ)).im = 0)
    (heq : ∀ t ∈ Icc a b, ∀ ε : ℝ, 0 < ε →
      E ((t : ℂ)+(ε : ℂ)*Complex.I) =
        TeschlQM.Herglotz.borelTransform μ ((t : ℂ)+(ε : ℂ)*Complex.I)) :
    μ (Icc a b) = 0 := by
  have hc : Continuous (fun ε : ℝ => (1/Real.pi)*(∫ t in a..b,
      (E ((t:ℂ)+(ε:ℂ)*Complex.I)).im)) := by
    apply Continuous.const_mul
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact Complex.continuous_im.comp (hE.comp (by fun_prop))
  have hz : (1/Real.pi)*(∫ t in a..b, (E ((t:ℂ)+(0:ℂ)*Complex.I)).im) = 0 := by
    simp [hreal]
  have hlim : Tendsto (fun ε : ℝ => (1/Real.pi)*(∫ t in a..b,
      (E ((t:ℂ)+(ε:ℂ)*Complex.I)).im)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Complex.ofReal_zero,hz] using (hc.tendsto 0).mono_left (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hlim' := TeschlQM.Herglotz.stieltjes_inversion_formula μ a b hab
  have hsame : (fun ε : ℝ => (1/Real.pi)*(∫ t in a..b,
      (E ((t:ℂ)+(ε:ℂ)*Complex.I)).im)) =ᶠ[𝓝[>] 0]
      (fun ε : ℝ => (1/Real.pi)*(∫ t in a..b,
      (TeschlQM.Herglotz.borelTransform μ ((t:ℂ)+(ε:ℂ)*Complex.I)).im)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hab.le] at ht
    exact congrArg Complex.im (heq t ht ε hε)
  have hv := tendsto_nhds_unique (hlim.congr' hsame) hlim'
  have hto : (μ (Icc a b)).toReal = 0 := by
    have h1 := ENNReal.toReal_nonneg (a := μ (Ioo a b))
    have h2 := ENNReal.toReal_nonneg (a := μ (Icc a b))
    linarith
  exact (ENNReal.toReal_eq_zero_iff _).mp hto |>.resolve_right (measure_ne_top μ _)



set_option autoImplicit false
namespace DerivativeChainPrivate

theorem sexticRadicand_im_identity (a b c : ℝ) (z : ℂ) (hz : z ≠ 0) :
    (sexticRadicand a b c z).im*(z.re^2+z.im^2) =
      z.im*((2*z.re+a)*(z.re^2+z.im^2)-c) := by
  have hd : z.re^2+z.im^2 ≠ 0 := by
    simpa [Complex.normSq_apply,pow_two] using ne_of_gt (Complex.normSq_pos.mpr hz)
  simp only [sexticRadicand,pow_two,Complex.add_im,Complex.mul_im,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.div_im]
  simp only [Complex.normSq_apply]
  field_simp
  ring

theorem sexticRadicand_real (a b c x : ℝ) :
    sexticRadicand a b c (x : ℂ) = ((x^2+a*x+b+c/x : ℝ) : ℂ) := by
  simp [sexticRadicand]





theorem sexticRadicand_slit_exterior (a b c : ℝ)
    (ha : -11/5 ≤ a) (ha0 : a < 0) (hc : 0 < c) (hc1 : c ≤ 1)
    (hreal : ∀ x : ℝ, x ≤ -1/4 ∨ 3/2 ≤ x → 0 < x^2+a*x+b+c/x)
    (z : ℂ) (hz : z.re ≤ -1/4 ∨ 3/2 ≤ z.re) :
    sexticRadicand a b c z ∈ Complex.slitPlane := by
  have hz0 : z ≠ 0 := by intro he; simp [he] at hz; rcases hz with h|h <;> norm_num at h
  rw [Complex.mem_slitPlane_iff]
  by_cases hi : z.im = 0
  · left
    have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hi]
    rw [he,sexticRadicand_real,Complex.ofReal_re]
    exact hreal _ hz
  · right
    have hid := sexticRadicand_im_identity a b c z hz0
    intro hzero
    rw [hzero,zero_mul] at hid
    have hfactor : (2*z.re+a)*(z.re^2+z.im^2)-c=0 :=
      (mul_eq_zero.mp hid.symm).resolve_left hi
    have hd : 0 < z.re^2+z.im^2 := by positivity
    rcases hz with hl|hr
    · have hf : 2*z.re+a < 0 := by linarith
      have hp := mul_neg_of_neg_of_pos hf hd
      linarith
    · have hf : 4/5 ≤ 2*z.re+a := by linarith
      have hd' : 9/4 ≤ z.re^2+z.im^2 := by nlinarith [sq_nonneg z.im]
      have hp := mul_le_mul hf hd' (by norm_num : (0:ℝ) ≤ 9/4) (by linarith : 0 ≤ 2*z.re+a)
      nlinarith

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open MeasureTheory Set

theorem sextic_measure_ae_interval (μ : Measure ℝ)
    (hi : ∀ L U : ℝ, L < U → U ≤ -1/4 ∨ 3/2 ≤ L → μ (Icc L U) = 0) :
    ∀ᵐ x ∂μ, x ∈ Icc (-1/4 : ℝ) (3/2) := by
  let s : ℕ → Set ℝ := fun n => Icc (-(n+1:ℝ)) (-1/4) ∪ Icc (3/2) (n+2:ℝ)
  have hs : ∀ n, μ (s n) = 0 := by
    intro n
    apply measure_union_null
    · exact hi _ _ (by have := Nat.cast_nonneg (α:=ℝ) n; linarith) (Or.inl le_rfl)
    · exact hi _ _ (by have := Nat.cast_nonneg (α:=ℝ) n; linarith) (Or.inr le_rfl)
  have hu : μ (⋃ n, s n) = 0 := measure_iUnion_null hs
  apply ae_iff.mpr
  apply measure_mono_null (t := ⋃ n, s n) _ hu
  intro x hx
  change ¬(-1/4 ≤ x ∧ x ≤ 3/2) at hx
  obtain ⟨n,hn⟩ := exists_nat_gt |x|
  apply mem_iUnion.mpr
  refine ⟨n,?_⟩
  dsimp only [s]
  rcases not_and_or.mp hx with h|h
  · left
    constructor
    · have := neg_abs_le x; linarith
    · linarith
  · right
    constructor
    · linarith
    · have := le_abs_self x; linarith





end DerivativeChainPrivate



set_option autoImplicit false
open Set
namespace DerivativeChainPrivate







theorem sexticUpperBranch_sq (a b c : ℝ) (z : ℂ) :
    (sexticUpperBranch a b c z)^2 = sexticRadicand a b c z := by
  rw [sexticUpperBranch,mul_pow]
  have hs : (Complex.sqrt (-sexticRadicand a b c z))^2 = -sexticRadicand a b c z :=
    Complex.cpow_nat_inv_pow _ (by norm_num : (2 : ℕ) ≠ 0)
  rw [hs,Complex.I_sq]
  ring

theorem sexticUpperBranch_im_pos (a b c : ℝ) (z : ℂ)
    (havoid : (sexticRadicand a b c z).im ≠ 0 ∨ (sexticRadicand a b c z).re < 0) :
    0 < (sexticUpperBranch a b c z).im := by
  simp only [sexticUpperBranch,Complex.mul_im,Complex.I_re,Complex.I_im,
    one_mul,zero_mul,zero_add]
  rw [Complex.sqrt,Complex.cpow_inv_two_re]
  apply Real.sqrt_pos.mpr
  rcases havoid with hi | hr
  · have hn := Complex.abs_re_lt_norm.mpr (show (-sexticRadicand a b c z).im ≠ 0 by simpa using hi)
    have ha := neg_abs_le (-sexticRadicand a b c z).re
    linarith
  · simp only [Complex.neg_re]
    have hn := norm_nonneg (-sexticRadicand a b c z)
    linarith

theorem real_quadratic_nonnegative_discriminant_root_im (A B C : ℝ)
    (hC : C ≠ 0) (hD : 0 ≤ B^2-4*A*C) (z : ℂ)
    (hroot : (A : ℂ)*z^2+(B : ℂ)*z+(C : ℂ)=0) : z.im = 0 := by
  by_contra hy
  have hre := congrArg Complex.re hroot
  have him := congrArg Complex.im hroot
  simp only [pow_two,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.zero_re,Complex.zero_im,
    zero_mul,mul_zero,zero_add,add_zero,sub_zero] at hre him
  have hm : z.im*(2*A*z.re+B)=0 := by nlinarith only [him]
  have hl := (mul_eq_zero.mp hm).resolve_left hy
  have hA : A ≠ 0 := by
    intro ha
    rw [ha] at hl hre
    have hb : B = 0 := by simpa using hl
    apply hC
    simpa [hb] using hre
  have heq : B^2-4*A*C = -4*A^2*z.im^2 := by
    linear_combination (2*A*z.re+B)*hl-4*A*hre
  have hpos := mul_pos (sq_pos_of_ne_zero hA) (sq_pos_of_ne_zero hy)
  nlinarith only [heq,hD,hpos]

theorem sexticShift_im_ne_zero (a b c : ℝ) (hc : c ≠ 0)
    (hD : ∀ v : ℝ, 0 ≤ ((a/2+v)^2-b)^2+8*c*v)
    (z : ℂ) (hz : 0 < z.im) : (sexticShift a b c z).im ≠ 0 := by
  intro hzero
  let v := (sexticShift a b c z).re
  have hreal : sexticShift a b c z = (v : ℂ) := by apply Complex.ext <;> simp [v,hzero]
  have hF : sexticUpperBranch a b c z = z+((a/2 : ℝ) : ℂ)+(v : ℂ) := by
    dsimp only [sexticShift] at hreal
    linear_combination hreal
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hs := sexticUpperBranch_sq a b c z
  rw [hF] at hs
  have hquad : ((2*v : ℝ) : ℂ)*z^2+(((a/2+v)^2-b : ℝ) : ℂ)*z+((-c : ℝ) : ℂ)=0 := by
    calc
      _ = z*((z+((a/2 : ℝ) : ℂ)+(v : ℂ))^2-sexticRadicand a b c z) := by
        dsimp only [sexticRadicand]
        push_cast
        field_simp
        ring
      _ = 0 := by rw [hs]; ring
  have hd : 0 ≤ ((a/2+v)^2-b)^2-4*(2*v)*(-c) := by
    convert hD v using 1 <;> ring
  have hi := real_quadratic_nonnegative_discriminant_root_im (2*v) ((a/2+v)^2-b) (-c)
    (neg_ne_zero.mpr hc) hd z hquad
  linarith

theorem sexticShift_differentiableAt (a b c : ℝ) (z : ℂ) (hz : 0 < z.im)
    (havoid : (sexticRadicand a b c z).im ≠ 0 ∨ (sexticRadicand a b c z).re < 0) :
    DifferentiableAt ℂ (sexticShift a b c) z := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hslit : -sexticRadicand a b c z ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    rcases havoid with hi | hr
    · right; simpa using hi
    · left; simpa using neg_pos.mpr hr
  have hh : DifferentiableAt ℂ (sexticRadicand a b c) z := by
    unfold sexticRadicand
    fun_prop
  have hs : DifferentiableAt ℂ (fun w => Complex.sqrt (-sexticRadicand a b c w)) z := by
    simpa only [Function.comp_def, Pi.neg_apply] using
      (Complex.differentiableAt_sqrt hslit).comp z hh.neg
  have hf : DifferentiableAt ℂ (sexticUpperBranch a b c) z := by
    exact (differentiableAt_const Complex.I).mul hs
  exact (hf.sub differentiableAt_id).sub (differentiableAt_const ((a/2 : ℝ) : ℂ))

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate

theorem sqrt_im_sign (w : ℂ) (hw : w.im ≠ 0) :
    0 < (Complex.sqrt w).re ∧ (Complex.sqrt w).im * w.im > 0 := by
  have hs : (Complex.sqrt w)^2 = w := Complex.cpow_nat_inv_pow _ (by norm_num : (2:ℕ) ≠ 0)
  have hr : 0 < (Complex.sqrt w).re := by
    rw [Complex.sqrt,Complex.cpow_inv_two_re]
    apply Real.sqrt_pos.mpr
    have hn := Complex.abs_re_lt_norm.mpr hw
    have ha := neg_abs_le w.re
    linarith
  have hi := congrArg Complex.im hs
  simp only [pow_two,Complex.mul_im] at hi
  have hsi : (Complex.sqrt w).im ≠ 0 := by intro he; simp [he] at hi; exact hw hi.symm
  have hp := mul_pos hr (sq_pos_of_ne_zero hsi)
  constructor
  · exact hr
  · have he := congrArg (fun x : ℝ => (Complex.sqrt w).im*x) hi
    nlinarith only [he,hp]

theorem sexticUpperBranch_eq_sqrt_of_im_pos (a b c : ℝ) (z : ℂ)
    (hi : 0 < (sexticRadicand a b c z).im) :
    sexticUpperBranch a b c z = Complex.sqrt (sexticRadicand a b c z) := by
  have hF := sexticUpperBranch_im_pos a b c z (Or.inl (ne_of_gt hi))
  have hS := (sqrt_im_sign _ (ne_of_gt hi)).2
  have hSpos : 0 < (Complex.sqrt (sexticRadicand a b c z)).im := by nlinarith
  have hs : (Complex.sqrt (sexticRadicand a b c z))^2 = sexticRadicand a b c z :=
    Complex.cpow_nat_inv_pow _ (by norm_num : (2:ℕ) ≠ 0)
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp ((sexticUpperBranch_sq a b c z).trans hs.symm) with h|h
  · exact h
  · have hh := congrArg Complex.im h
    simp only [Complex.neg_im] at hh
    linarith

theorem sexticUpperBranch_eq_neg_sqrt_of_im_neg (a b c : ℝ) (z : ℂ)
    (hi : (sexticRadicand a b c z).im < 0) :
    sexticUpperBranch a b c z = -Complex.sqrt (sexticRadicand a b c z) := by
  have hF := sexticUpperBranch_im_pos a b c z (Or.inl (ne_of_lt hi))
  have hS := (sqrt_im_sign _ (ne_of_lt hi)).2
  have hSneg : (Complex.sqrt (sexticRadicand a b c z)).im < 0 := by nlinarith
  have hs : (Complex.sqrt (sexticRadicand a b c z))^2 = sexticRadicand a b c z :=
    Complex.cpow_nat_inv_pow _ (by norm_num : (2:ℕ) ≠ 0)
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp ((sexticUpperBranch_sq a b c z).trans hs.symm) with h|h
  · have hh := congrArg Complex.im h
    linarith
  · exact h

theorem sexticRadicand_im_right (a b c : ℝ) (ha : -11/5 ≤ a) (hc : c ≤ 1)
    (z : ℂ) (hx : 3/2 ≤ z.re) (hy : 0 < z.im) :
    0 < (sexticRadicand a b c z).im := by
  have hz0 : z ≠ 0 := by intro he; simp [he] at hy
  have hd : 0 < z.re^2+z.im^2 := by positivity
  have hf : 4/5 ≤ 2*z.re+a := by linarith
  have hd' : 9/4 ≤ z.re^2+z.im^2 := by nlinarith [sq_nonneg z.im]
  have hp := mul_le_mul hf hd' (by norm_num : (0:ℝ) ≤ 9/4) (by linarith : 0 ≤ 2*z.re+a)
  have hfpos : 0 < (2*z.re+a)*(z.re^2+z.im^2)-c := by nlinarith
  have hi := sexticRadicand_im_identity a b c z hz0
  have hm := mul_pos hy hfpos
  nlinarith

theorem sexticRadicand_im_left (a b c : ℝ) (ha : a < 0) (hc : 0 < c)
    (z : ℂ) (hx : z.re ≤ -1/4) (hy : 0 < z.im) :
    (sexticRadicand a b c z).im < 0 := by
  have hz0 : z ≠ 0 := by intro he; simp [he] at hy
  have hd : 0 < z.re^2+z.im^2 := by positivity
  have hf : 2*z.re+a < 0 := by linarith
  have hp := mul_neg_of_neg_of_pos hf hd
  have hfneg : (2*z.re+a)*(z.re^2+z.im^2)-c < 0 := by linarith
  have hi := sexticRadicand_im_identity a b c z hz0
  have hm := mul_neg_of_pos_of_neg hy hfneg
  nlinarith

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate

theorem sexticShift_growth (a b c : ℝ)
    (ha : |a| ≤ 3) (hb : |b| ≤ 2) (hc : |c| ≤ 1)
    (hE : |a^2/4-b| ≤ 2)
    (z : ℂ) (hz : 0 < z.im) (hG : 0 < (sexticShift a b c z).im) :
    ‖sexticShift a b c z‖ ≤ 10/z.im := by
  let F := sexticUpperBranch a b c z
  let G := sexticShift a b c z
  let r := ‖z‖
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hr : 0 < r := norm_pos_iff.mpr hz0
  have hy : z.im ≤ r := Complex.im_le_norm z
  have hF := sexticUpperBranch_sq a b c z
  have hFn : ‖F‖^2 = ‖sexticRadicand a b c z‖ := by
    simpa only [norm_pow] using congrArg norm hF
  have hGn : ‖G‖ ≤ ‖F‖+r+|a|/2 := by
    calc
      ‖G‖ ≤ ‖F-z‖+‖((a/2 : ℝ) : ℂ)‖ := norm_sub_le _ _
      _ ≤ ‖F‖+‖z‖+‖((a/2 : ℝ) : ℂ)‖ := by gcongr; exact norm_sub_le _ _
      _ = _ := by simp [r,Complex.norm_real,Real.norm_eq_abs,abs_div]
  have hnF := norm_nonneg F
  have hnG := norm_nonneg G
  apply (le_div_iff₀ hz).mpr
  change ‖G‖*z.im ≤ 10
  by_cases hlarge : 1 ≤ r
  · let D := F+z+((a/2 : ℝ) : ℂ)
    have hDi : 2*z.im ≤ D.im := by
      change 0 < (F-z-((a/2:ℝ):ℂ)).im at hG
      dsimp only [D]
      simp only [Complex.add_im,Complex.sub_im,Complex.ofReal_im] at hG ⊢
      linarith
    have hDn : 2*z.im ≤ ‖D‖ := hDi.trans (Complex.im_le_norm D)
    have hprod : G*D = ((b-a^2/4 : ℝ) : ℂ)+(c : ℂ)/z := by
      dsimp only [G,D,sexticShift,F]
      calc
        _ = (sexticUpperBranch a b c z)^2-z^2-(a:ℂ)*z-((a/2:ℝ):ℂ)^2 := by push_cast; ring
        _ = _ := by rw [hF]; unfold sexticRadicand; push_cast; ring
    have hpn : ‖G‖*‖D‖ ≤ 3 := by
      rw [← norm_mul,hprod]
      calc
        _ ≤ ‖((b-a^2/4:ℝ):ℂ)‖+‖(c:ℂ)/z‖ := norm_add_le _ _
        _ = |a^2/4-b|+|c|/r := by simp only [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_sub_comm]; rfl
        _ ≤ 2+1 := add_le_add hE ((div_le_iff₀ hr).mpr (by nlinarith))
        _ = 3 := by norm_num
    have hm := mul_le_mul_of_nonneg_left hDn hnG
    nlinarith only [hpn,hm]
  · have hsmall : r ≤ 1 := le_of_not_ge hlarge
    have hH : ‖sexticRadicand a b c z‖ ≤ r^2+|a| *r+|b|+|c|/r := by
      unfold sexticRadicand
      calc
        _ ≤ ‖z^2+(a:ℂ)*z+(b:ℂ)‖+‖(c:ℂ)/z‖ := norm_add_le _ _
        _ ≤ ‖z^2+(a:ℂ)*z‖+‖(b:ℂ)‖+‖(c:ℂ)/z‖ := by gcongr; exact norm_add_le _ _
        _ ≤ ‖z^2‖+‖(a:ℂ)*z‖+‖(b:ℂ)‖+‖(c:ℂ)/z‖ := by gcongr; exact norm_add_le _ _
        _ = _ := by simp [r,norm_pow,norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs]
    have hH' : ‖F‖^2*r ≤ r^3+|a| *r^2+|b| *r+|c| := by
      rw [← hFn] at hH
      have hm := mul_le_mul_of_nonneg_right hH (le_of_lt hr)
      have he : (r^2+|a| *r+|b|+|c|/r)*r = r^3+|a| *r^2+|b| *r+|c| := by field_simp
      rwa [he] at hm
    have hr2 : r^2 ≤ 1 := by nlinarith
    have hr3 : r^3 ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_right hr2 (le_of_lt hr)]
    have ha' : |a| *r^2 ≤ 3 := (mul_le_mul_of_nonneg_left hr2 (abs_nonneg a)).trans (by simpa using ha)
    have hb' : |b| *r ≤ 2 := (mul_le_mul_of_nonneg_left hsmall (abs_nonneg b)).trans (by simpa using hb)
    have hbound : ‖F‖^2*r ≤ 7 := by linarith
    have hrr := mul_le_mul_of_nonneg_left hsmall (mul_nonneg (sq_nonneg ‖F‖) (le_of_lt hr))
    have hFr : ‖F‖*r ≤ 3 := by nlinarith
    have hGr := mul_le_mul_of_nonneg_right hGn (le_of_lt hr)
    have ha2 := mul_le_mul_of_nonneg_right ha (le_of_lt hr)
    have hGy := mul_le_mul_of_nonneg_left hy hnG
    nlinarith only [hFr,hGr,ha2,hGy,hsmall,hr2]

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





theorem sexticShift_im_I_pos (a b c : ℝ) (hb : 0 ≤ b)
    (hgap : 4*b < (a-c)^2)
    (havoid : (sexticRadicand a b c Complex.I).im ≠ 0 ∨
      (sexticRadicand a b c Complex.I).re < 0) :
    0 < (sexticShift a b c Complex.I).im := by
  have hpos := sexticUpperBranch_im_pos a b c Complex.I havoid
  have hs := sexticUpperBranch_sq a b c Complex.I
  have hr := congrArg Complex.re hs
  have hi := congrArg Complex.im hs
  simp only [sexticRadicand, Complex.I_sq, Complex.div_I, Complex.add_re,
    Complex.add_im,Complex.neg_re,Complex.neg_im,Complex.one_re,Complex.one_im,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,zero_mul,mul_zero,mul_one,one_mul,sub_zero,zero_add,add_zero] at hr hi
  simp only [sexticShift,Complex.sub_im,Complex.I_im,Complex.ofReal_im,sub_zero]
  by_contra h
  have hy : (sexticUpperBranch a b c Complex.I).im ≤ 1 := by linarith
  have hy2 : (sexticUpperBranch a b c Complex.I).im^2 ≤ 1 := by nlinarith
  have hx2 : (sexticUpperBranch a b c Complex.I).re^2 ≤ b := by
    simp only [pow_two,Complex.mul_re] at hr
    nlinarith
  have hprod := mul_le_mul_of_nonneg_left hy2 (sq_nonneg (sexticUpperBranch a b c Complex.I).re)
  simp only [pow_two,Complex.mul_im] at hi
  have hsquare := congrArg (fun x : ℝ => x^2) hi
  nlinarith only [hsquare,hgap,hprod,hx2]

theorem sexticShift_im_pos (a b c : ℝ) (hc : c ≠ 0) (hb : 0 ≤ b)
    (hgap : 4*b < (a-c)^2)
    (hD : ∀ v : ℝ, 0 ≤ ((a/2+v)^2-b)^2+8*c*v)
    (havoid : ∀ z : ℂ, 0 < z.im →
      (sexticRadicand a b c z).im ≠ 0 ∨ (sexticRadicand a b c z).re < 0)
    (z : ℂ) (hz : 0 < z.im) : 0 < (sexticShift a b c z).im := by
  have hI : 0 < Complex.I.im := by norm_num
  have hseed := sexticShift_im_I_pos a b c hb hgap (havoid _ hI)
  have hcont : ContinuousOn (fun w : ℂ => (sexticShift a b c w).im) {w | 0 < w.im} := by
    intro w hw
    exact (Complex.continuous_im.continuousAt.comp
      (sexticShift_differentiableAt a b c w hw (havoid w hw)).continuousAt).continuousWithinAt
  have hconv : Convex ℝ {w : ℂ | 0 < w.im} :=
    (convex_Ioi (0 : ℝ)).linear_preimage Complex.imLm
  by_contra h
  have hzle : (sexticShift a b c z).im ≤ 0 := le_of_not_gt h
  obtain ⟨w,hw,hew⟩ := hconv.isPreconnected.intermediate_value hz hI hcont ⟨hzle,le_of_lt hseed⟩
  exact sexticShift_im_ne_zero a b c hc hD w hw hew

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open MeasureTheory TeschlQM.Herglotz

theorem sexticShift_measure (a b c : ℝ) (hc0 : c ≠ 0) (hb0 : 0 ≤ b)
    (hgap : 4*b < (a-c)^2)
    (hD : ∀ v : ℝ, 0 ≤ ((a/2+v)^2-b)^2+8*c*v)
    (havoid : ∀ z : ℂ, 0 < z.im →
      (sexticRadicand a b c z).im ≠ 0 ∨ (sexticRadicand a b c z).re < 0)
    (ha : |a| ≤ 3) (hb : |b| ≤ 2) (hc : |c| ≤ 1) (hE : |a^2/4-b| ≤ 2) :
    ∃ μ : Measure ℝ, μ Set.univ ≤ ENNReal.ofReal 10 ∧
      ∀ z : ℂ, 0 < z.im → sexticShift a b c z = borelTransform μ z := by
  apply TeschlQM.Herglotz.herglotz_representation
  · constructor
    · intro z hz
      exact (sexticShift_differentiableAt a b c z hz (havoid z hz)).differentiableWithinAt
    · exact sexticShift_im_pos a b c hc0 hb0 hgap hD havoid
  · intro z hz
    exact sexticShift_growth a b c ha hb hc hE z hz
      (sexticShift_im_pos a b c hc0 hb0 hgap hD havoid z hz)





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open MeasureTheory Set



theorem sexticExteriorExtension_continuous (a b c σ : ℝ) (f : ℝ → ℝ)
    (hf : Continuous f)
    (hf0 : ∀ x, f x ≠ 0)
    (hslit : ∀ z : ℂ, sexticRadicand a b c ((f z.re:ℂ)+Complex.I*(z.im:ℂ)) ∈ Complex.slitPlane) :
    Continuous (sexticExteriorExtension a b c σ f) := by
  have hw : Continuous (fun z : ℂ => ((f z.re:ℂ)+Complex.I*(z.im:ℂ))) := by fun_prop
  have hw0 : ∀ z : ℂ, ((f z.re:ℂ)+Complex.I*(z.im:ℂ)) ≠ 0 := by
    intro z h
    have hr := congrArg Complex.re h
    simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,
      Complex.I_im,Complex.ofReal_im,zero_mul,mul_zero,sub_self,add_zero,Complex.zero_re] at hr
    exact hf0 _ hr
  have hH : Continuous (fun z : ℂ => sexticRadicand a b c ((f z.re:ℂ)+Complex.I*(z.im:ℂ))) := by
    unfold sexticRadicand
    fun_prop
  have hs : Continuous (fun z : ℂ => Complex.sqrt (sexticRadicand a b c ((f z.re:ℂ)+Complex.I*(z.im:ℂ)))) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    simpa only [Function.comp_def] using
      ContinuousAt.comp (f := fun w : ℂ => sexticRadicand a b c ((f w.re:ℂ)+Complex.I*(w.im:ℂ)))
        (Complex.differentiableAt_sqrt (hslit z)).continuousAt (hH.continuousAt (x := z))
  unfold sexticExteriorExtension
  fun_prop

theorem sexticExteriorExtension_real (a b c σ : ℝ) (f : ℝ → ℝ)
    (hr : ∀ x, 0 < (f x)^2+a*(f x)+b+c/(f x)) (x : ℝ) :
    (sexticExteriorExtension a b c σ f (x:ℂ)).im = 0 := by
  simp only [sexticExteriorExtension,Complex.ofReal_re,Complex.ofReal_im,
    Complex.ofReal_zero,mul_zero,add_zero,sexticRadicand_real]
  rw [Complex.sqrt_of_nonneg (by exact_mod_cast (hr x).le)]
  simp

theorem sextic_measure_exterior_intervals (a b c : ℝ)
    (ha : -11/5 ≤ a) (ha0 : a < 0) (hc : 0 < c) (hc1 : c ≤ 1)
    (hreal : ∀ x : ℝ, x ≤ -1/4 ∨ 3/2 ≤ x → 0 < x^2+a*x+b+c/x)
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : ∀ z : ℂ, 0 < z.im → sexticShift a b c z = TeschlQM.Herglotz.borelTransform μ z)
    (L U : ℝ) (hLU : L < U) (hside : U ≤ -1/4 ∨ 3/2 ≤ L) :
    μ (Icc L U) = 0 := by
  rcases hside with hl | hr
  · let f : ℝ → ℝ := fun x => min (-1/4) x
    have hf : ∀ x, f x ≤ -1/4 := fun x => min_le_left _ _
    have hf0 : ∀ x, f x ≠ 0 := by intro x; have := hf x; linarith
    have hE := sexticExteriorExtension_continuous a b c (-1) f (by dsimp [f]; fun_prop) hf0
      (fun z => sexticRadicand_slit_exterior a b c ha ha0 hc hc1 hreal _
        (Or.inl (by simpa using hf z.re)))
    apply measure_Icc_zero_of_real_extension μ L U hLU (sexticExteriorExtension a b c (-1) f) hE
    · exact sexticExteriorExtension_real a b c (-1) f (fun x => hreal _ (Or.inl (hf x)))
    · intro t ht ε hε
      have ht' : t ≤ -1/4 := ht.2.trans hl
      have hfr : f t = t := min_eq_right ht'
      have hz : 0 < ((t:ℂ)+(ε:ℂ)*Complex.I).im := by simpa using hε
      rw [← hμ _ hz]
      unfold sexticExteriorExtension sexticShift
      simp only [Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
        Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,
        zero_mul,zero_add,sub_zero,add_zero,hfr,Complex.ofReal_neg,Complex.ofReal_one,neg_one_mul]
      rw [sexticUpperBranch_eq_neg_sqrt_of_im_neg a b c _
        (sexticRadicand_im_left a b c ha0 hc _ (by simpa) hz)]
      congr 2 <;> ring
  · let f : ℝ → ℝ := fun x => max (3/2) x
    have hf : ∀ x, 3/2 ≤ f x := fun x => le_max_left _ _
    have hf0 : ∀ x, f x ≠ 0 := by intro x; have := hf x; linarith
    have hE := sexticExteriorExtension_continuous a b c 1 f (by dsimp [f]; fun_prop) hf0
      (fun z => sexticRadicand_slit_exterior a b c ha ha0 hc hc1 hreal _
        (Or.inr (by simpa using hf z.re)))
    apply measure_Icc_zero_of_real_extension μ L U hLU (sexticExteriorExtension a b c 1 f) hE
    · exact sexticExteriorExtension_real a b c 1 f (fun x => hreal _ (Or.inr (hf x)))
    · intro t ht ε hε
      have ht' : 3/2 ≤ t := hr.trans ht.1
      have hfr : f t = t := max_eq_right ht'
      have hz : 0 < ((t:ℂ)+(ε:ℂ)*Complex.I).im := by simpa using hε
      rw [← hμ _ hz]
      unfold sexticExteriorExtension sexticShift
      simp only [Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
        Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,
        zero_mul,zero_add,sub_zero,add_zero,hfr,Complex.ofReal_one,one_mul]
      rw [sexticUpperBranch_eq_sqrt_of_im_pos a b c _
        (sexticRadicand_im_right a b c ha hc1 _ (by simpa) hz)]
      congr 2 <;> ring

end DerivativeChainPrivate


set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DerivativeChainPrivate
open Polynomial MeasureTheory Set TeschlQM.Herglotz





theorem sixth_sextic_level_discriminant (v : ℝ) :
    0 ≤ (((-85/43 : ℝ)/2+v)^2-1445/1806)^2+8*(24565/211302)*v := by
  by_cases hv : 0 ≤ v
  · positivity
  · have hv' : v ≤ 0 := le_of_not_ge hv
    have hv3 : 0 ≤ (-v)^3 := pow_nonneg (neg_nonneg.mpr hv') 3
    nlinarith only [sq_nonneg (2*v+3/20), sq_nonneg v, hv3, sq_nonneg (v^2), hv']



theorem sixth_sextic_positive_measure :
    ∃ μ : Measure ℝ, μ Set.univ ≤ ENNReal.ofReal 10 ∧
      ∀ z : ℂ, 0 < z.im →
        sexticShift (-85/43) (1445/1806) (24565/211302) z = borelTransform μ z := by
  apply sexticShift_measure (-85/43) (1445/1806) (24565/211302)
    (by norm_num) (by norm_num) (by norm_num) sixth_sextic_level_discriminant
  · intro z hz
    simpa [sexticRadicand] using sixth_sextic_radicand_avoids_nonnegative z hz
  all_goals norm_num

theorem sixth_sextic_compact_positive_measure :
    ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧
      (∀ᵐ x ∂μ, x ∈ Icc (-1/4 : ℝ) (3/2)) ∧
      ∀ z : ℂ, 0 < z.im →
        sexticShift (-85/43) (1445/1806) (24565/211302) z = TeschlQM.Herglotz.borelTransform μ z := by
  obtain ⟨μ,hm,hrep⟩ := sixth_sextic_positive_measure
  haveI : IsFiniteMeasure μ := ⟨lt_of_le_of_lt hm ENNReal.ofReal_lt_top⟩
  refine ⟨μ,inferInstance,?_,hrep⟩
  apply sextic_measure_ae_interval μ
  exact sextic_measure_exterior_intervals (-85/43) (1445/1806) (24565/211302)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    sixth_sextic_real_exterior μ hrep







end DerivativeChainPrivate

theorem solution (β w : ℂ) (hR : 0 ≤ β.re) (hI : 0 < β.im)
    (hwpos : 0 < w.re) (hwim : 0 ≤ w.im) (hwX : 5/2 ≤ w.re^2)
    (hwroot : w^5-(10/3)*w^3-10*β*w^2+(85/48)*w+(85/21)*β=0)
    (hwinv : β/w = (1/10:ℂ)*w^2-41/140+(459/7840:ℂ)/(w^2-17/42)) :
    ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧
      (∀ᵐ t ∂μ, t ∈ Icc (-1/4:ℝ) (3/2)) ∧
      (∀ u : ℂ, 0 < u.im → sexticShift (-85/43) (1445/1806) (24565/211302) u =
        TeschlQM.Herglotz.borelTransform μ u) ∧
      ∃ z : ℂ,
        (1360/91)*β^2-20*β*z^3+(170/7)*β*z+z^6-5*z^4+(85/16)*z^2-1445/2184=0 ∧
        w.re ≤ z.re ∧ w.im ≤ z.im ∧ 0 < z.im ∧ 7/2 < z.re^2 ∧
        β/z = (((455-3*Real.sqrt 19565)/680:ℝ):ℂ)*z^2-(((559-3*Real.sqrt 19565)/688:ℝ):ℂ)+
          ((3*Real.sqrt 19565/680:ℝ):ℂ)*(∫ t : ℝ, (z^2-(t:ℂ))⁻¹ ∂μ) := by
  obtain ⟨z,hz,hr,hi⟩ := normalized_sixth_sextic_step β w hR hI.le hwpos hwim hwX hwroot hwinv
  have hx : 0 < z.re := lt_of_lt_of_le hwpos hr
  have hX : 5/2 ≤ z.re^2 := by nlinarith only [hwX,hwpos,hr]
  obtain ⟨μ,hfinite,hsupp,hμ⟩ := sixth_sextic_compact_positive_measure
  letI : IsFiniteMeasure μ := hfinite
  obtain ⟨hy0,hzero⟩ := sixth_sextic_nonnegative_im μ hsupp hμ β z hR hI.le hx hX hz
  have hy : 0 < z.im := by
    by_contra hn
    have he : z.im=0 := le_antisymm (le_of_not_gt hn) hy0
    have := hzero.mpr he
    linarith
  have hg := sixth_sextic_selected_graph μ hsupp hμ β w z hR hI.le hwpos hwim hwX hwinv hr hy hz
  have hloc := sixth_sextic_selected_localization μ hsupp hμ β z hR hx hy hX hg
  exact ⟨μ,hfinite,hsupp,hμ,z,hz,hr,hi,hy,hloc,hg⟩
