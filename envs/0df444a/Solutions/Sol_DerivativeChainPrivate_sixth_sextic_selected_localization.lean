-- Prove2me | solution 1 for DerivativeChainPrivate.sixth_sextic_selected_localization
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T05:03:03.150194+00:00
-- url     : https://prove2.me/submissions/26c188d7-155b-4547-ad27-49e8928391cc

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChainPrivate_higher_power_radicals
import Definitions.Def_TeschlQM_Herglotz_borelTransform
import Theorems.Thm_DerivativeChainPrivate_cubic_graph_coordinate_parts
import Theorems.Thm_DerivativeChainPrivate_rational_inverse_parts
import Theorems.Thm_DerivativeChainPrivate_sixth_sextic_real_exterior
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





end DerivativeChainPrivate



set_option autoImplicit false
open MeasureTheory Filter Set
open scoped Topology
namespace DerivativeChainPrivate

theorem borelTransform_vertical_limit (μ : Measure ℝ) [IsFiniteMeasure μ]
    (B T : ℝ) (hT : B < T) (hμ : ∀ᵐ t ∂μ, t ≤ B) :
    Tendsto (fun ε : ℝ => TeschlQM.Herglotz.borelTransform μ ((T:ℂ)+(ε:ℂ)*Complex.I))
      (𝓝 0) (𝓝 (TeschlQM.Herglotz.borelTransform μ (T:ℂ))) := by
  unfold TeschlQM.Herglotz.borelTransform
  have hc : ContinuousAt (fun ε : ℝ => ∫ t : ℝ, ((t:ℂ)-((T:ℂ)+(ε:ℂ)*Complex.I))⁻¹ ∂μ) 0 := by
    apply continuousAt_of_dominated (bound := fun _ => (T-B)⁻¹)
    · exact Eventually.of_forall (fun ε => ((Complex.measurable_ofReal.sub_const _).inv).aestronglyMeasurable)
    · apply Eventually.of_forall
      intro ε
      filter_upwards [hμ] with t ht
      rw [norm_inv]
      apply inv_anti₀ (sub_pos.mpr hT)
      calc
        T-B ≤ T-t := by linarith
        _ ≤ |t-T| := by rw [abs_of_neg (by linarith : t-T < 0)]; ring_nf; rfl
        _ = |((t:ℂ)-((T:ℂ)+(ε:ℂ)*Complex.I)).re| := by simp
        _ ≤ ‖(t:ℂ)-((T:ℂ)+(ε:ℂ)*Complex.I)‖ := Complex.abs_re_le_norm _
    · exact integrable_const _
    · filter_upwards [hμ] with t ht
      apply ContinuousAt.inv₀ (by fun_prop)
      simp only [Complex.ofReal_zero,zero_mul,add_zero,sub_ne_zero]
      exact_mod_cast (show t ≠ T by linarith)
  simpa using hc.tendsto

theorem sextic_measure_real_value (a b c : ℝ)
    (ha : -11/5 ≤ a) (ha0 : a < 0) (hc : 0 < c) (hc1 : c ≤ 1)
    (hreal : ∀ x : ℝ, x ≤ -1/4 ∨ 3/2 ≤ x → 0 < x^2+a*x+b+c/x)
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : ∀ᵐ t ∂μ, t ∈ Icc (-1/4:ℝ) (3/2))
    (hμ : ∀ z : ℂ, 0 < z.im → sexticShift a b c z = TeschlQM.Herglotz.borelTransform μ z)
    (T : ℝ) (hT : 3/2 < T) :
    TeschlQM.Herglotz.borelTransform μ (T:ℂ) =
      ((Real.sqrt (T^2+a*T+b+c/T)-T-a/2 : ℝ):ℂ) := by
  let f : ℝ → ℝ := fun x => max (3/2) x
  let E := sexticExteriorExtension a b c 1 f
  have hf : ∀ x, 3/2 ≤ f x := fun x => le_max_left _ _
  have hf0 : ∀ x, f x ≠ 0 := by intro x; have := hf x; linarith
  have hE : Continuous E := sexticExteriorExtension_continuous a b c 1 f
    (by dsimp [f]; fun_prop) hf0 (fun z => sexticRadicand_slit_exterior a b c ha ha0 hc hc1 hreal _
      (Or.inr (by simpa using hf z.re)))
  have heq : ∀ ε : ℝ, 0 < ε → E ((T:ℂ)+(ε:ℂ)*Complex.I) =
      TeschlQM.Herglotz.borelTransform μ ((T:ℂ)+(ε:ℂ)*Complex.I) := by
    intro ε hε
    have hz : 0 < ((T:ℂ)+(ε:ℂ)*Complex.I).im := by simpa using hε
    rw [← hμ _ hz]
    dsimp only [E,sexticExteriorExtension,sexticShift]
    simp only [Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,
      zero_mul,zero_add,sub_zero,add_zero,Complex.ofReal_one,one_mul]
    rw [show f T = T by exact max_eq_right hT.le]
    rw [sexticUpperBranch_eq_sqrt_of_im_pos a b c _
      (sexticRadicand_im_right a b c ha hc1 _ (by simpa using hT.le) hz)]
    congr 2 <;> ring
  have hv : E (T:ℂ) = ((Real.sqrt (T^2+a*T+b+c/T)-T-a/2 : ℝ):ℂ) := by
    dsimp only [E,sexticExteriorExtension]
    simp only [Complex.ofReal_re,Complex.ofReal_im,Complex.ofReal_zero,mul_zero,add_zero,
      Complex.ofReal_one,one_mul]
    rw [show f T = T by exact max_eq_right hT.le,sexticRadicand_real]
    rw [Complex.sqrt_of_nonneg (by exact_mod_cast (hreal T (Or.inr hT.le)).le)]
    simp only [Complex.ofReal_re]
    push_cast
    rfl
  have hlim : Tendsto (fun ε : ℝ => E ((T:ℂ)+(ε:ℂ)*Complex.I)) (𝓝[>]0) (𝓝 (E (T:ℂ))) := by
    have ht : Tendsto (fun ε : ℝ => ((T:ℂ)+(ε:ℂ)*Complex.I)) (𝓝 0) (𝓝 (T:ℂ)) := by
      simpa using (show Continuous (fun ε : ℝ => ((T:ℂ)+(ε:ℂ)*Complex.I)) by fun_prop).tendsto 0
    exact (hE.continuousAt.tendsto.comp ht).mono_left nhdsWithin_le_nhds
  have hlim' := (borelTransform_vertical_limit μ (3/2) T hT (hsupp.mono fun t ht => ht.2)).mono_left
    (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hevent : (fun ε : ℝ => E ((T:ℂ)+(ε:ℂ)*Complex.I)) =ᶠ[𝓝[>]0]
      (fun ε : ℝ => TeschlQM.Herglotz.borelTransform μ ((T:ℂ)+(ε:ℂ)*Complex.I)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε using heq ε hε
  exact (tendsto_nhds_unique hlim' (hlim.congr' hevent)).trans hv

end DerivativeChainPrivate

namespace DerivativeChainPrivate
open MeasureTheory

theorem real_cauchy_integral_of_borel_value (μ : Measure ℝ) (T V : ℝ)
    (hV : TeschlQM.Herglotz.borelTransform μ (T:ℂ) = (V:ℂ)) :
    (∫ t : ℝ, 1/(T-t) ∂μ) = -V := by
  have hi : TeschlQM.Herglotz.borelTransform μ (T:ℂ) =
      -((∫ t : ℝ, 1/(T-t) ∂μ : ℝ):ℂ) := by
    unfold TeschlQM.Herglotz.borelTransform
    rw [← integral_complex_ofReal,← integral_neg]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun t => by
      push_cast
      rw [one_div,← inv_neg]
      congr 1
      ring)
  rw [hV] at hi
  have hr := congrArg Complex.re hi
  simp only [Complex.ofReal_re,Complex.neg_re] at hr
  linarith

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open MeasureTheory Set

theorem cauchy_root_kernel_bound (z : ℂ) (hx : 5/2 ≤ z.re^2) (t : ℝ)
    (ht : t ∈ Icc (-1/4:ℝ) (3/2)) :
    z^2-(t:ℂ) ≠ 0 ∧ ‖(z^2-(t:ℂ))⁻¹‖ ≤ (z.re^2-3/2)⁻¹ := by
  have htabs : |t| ≤ 3/2 := abs_le.mpr ⟨by linarith [ht.1],ht.2⟩
  have hn : z.re^2-3/2 ≤ ‖z^2-(t:ℂ)‖ := by
    have htri := norm_sub_norm_le (z^2) (t:ℂ)
    rw [norm_pow,Complex.norm_real,Real.norm_eq_abs] at htri
    have hsq : z.re^2 ≤ ‖z‖^2 := by
      rw [Complex.sq_norm,Complex.normSq_apply]
      nlinarith [sq_nonneg z.im]
    linarith
  have hp : 0 < z.re^2-3/2 := by linarith
  constructor
  · exact norm_pos_iff.mp (lt_of_lt_of_le hp hn)
  · rw [norm_inv]
    exact inv_anti₀ hp hn

theorem cauchy_kernel_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : ∀ᵐ t ∂μ, t ∈ Icc (-1/4:ℝ) (3/2))
    (z : ℂ) (hx : 5/2 ≤ z.re^2) :
    Integrable (fun t : ℝ => (z^2-(t:ℂ))⁻¹) μ := by
  apply Integrable.of_bound ((measurable_const.sub Complex.measurable_ofReal).inv).aestronglyMeasurable
    (z.re^2-3/2)⁻¹
  filter_upwards [hsupp] with t ht
  exact (cauchy_root_kernel_bound z hx t ht).2

theorem cauchy_root_kernel_parts (z : ℂ) (hxpos : 0 < z.re)
    (hx : 5/2 ≤ z.re^2) (t : ℝ) (ht : t ∈ Icc (-1/4:ℝ) (3/2)) :
    let D := (z.re^2-t)^2+2*(z.re^2+t)*z.im^2+z.im^4
    (z/(z^2-(t:ℂ))).re = z.re*((z.re^2+z.im^2-t)/D) ∧
    (z/(z^2-(t:ℂ))).im = -z.im*((z.re^2+z.im^2+t)/D) := by
  have hz : z ≠ 0 := by intro h; simp [h] at hxpos
  have hpole := (cauchy_root_kernel_bound z hx t ht).1
  obtain ⟨hr,hi,_,hd⟩ := rational_inverse_parts (z/(z^2-(t:ℂ))) z 0 0 1 t hz hpole
    (by simp; field_simp)
  simp only [Complex.ofReal_zero,Complex.ofReal_one,zero_mul,sub_zero,zero_add,one_mul,zero_sub] at hr hi
  have hd' : ‖z^2-(t:ℂ)‖^2 = (z.re^2-t)^2+2*(z.re^2+t)*z.im^2+z.im^4 := by
    rw [hd]; ring
  rw [hd'] at hr hi
  refine ⟨hr,?_⟩
  simpa only [mul_neg,neg_mul] using hi

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate

theorem sextic_kernel_bounds (X Y t T : ℝ) (hT : 5/2 ≤ T) (hX : T ≤ X)
    (hY : 0 ≤ Y) (htl : -1/4 ≤ t) (htu : t ≤ 3/2) :
    let D := (X-t)^2+2*(X+t)*Y+Y^2
    0 < D ∧ 0 ≤ (X+Y-t)/D ∧ 0 ≤ (X+Y+t)/D ∧
      0 ≤ (2*(X+Y)-t)/D ∧ (X+Y-t)/D ≤ 1/(T-t) := by
  have hXt : 0 < X-t := by linarith
  have hTt : 0 < T-t := by linarith
  have hXp : 0 < X+t := by linarith
  have hX3t : 0 < X+3*t := by linarith
  have hD : 0 < (X-t)^2+2*(X+t)*Y+Y^2 := by positivity
  refine ⟨hD,div_nonneg (by linarith) hD.le,div_nonneg (by linarith) hD.le,
    div_nonneg (by linarith) hD.le,?_⟩
  apply le_trans (b := 1/(X-t))
  · apply (div_le_div_iff₀ hD hXt).mpr
    have hp := mul_nonneg hX3t.le hY
    nlinarith only [hp,sq_nonneg Y]
  · exact one_div_le_one_div_of_le hTt (by linarith)








end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open MeasureTheory Set

theorem cauchy_real_kernel_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : ∀ᵐ t ∂μ, t ∈ Icc (-1/4:ℝ) (3/2)) (T : ℝ) (hT : 3/2 < T) :
    Integrable (fun t : ℝ => 1/(T-t)) μ := by
  have hm : Measurable (fun t : ℝ => 1/(T-t)) := measurable_const.div (measurable_const.sub measurable_id)
  apply Integrable.of_bound hm.aestronglyMeasurable (1/(T-3/2))
  filter_upwards [hsupp] with t ht
  have hp : 0 < T-t := by linarith [ht.2]
  rw [Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hp)]
  exact one_div_le_one_div_of_le (by linarith) (by linarith [ht.2])

theorem cauchy_root_corrections (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : ∀ᵐ t ∂μ, t ∈ Icc (-1/4:ℝ) (3/2))
    (z : ℂ) (hxpos : 0 < z.re) (hypos : 0 < z.im)
    (T : ℝ) (hT : 5/2 ≤ T) (hx : T ≤ z.re^2) :
    let E := z*(∫ t : ℝ, (z^2-(t:ℂ))⁻¹ ∂μ)
    0 ≤ E.re/z.re ∧ E.re/z.re ≤ ∫ t : ℝ, 1/(T-t) ∂μ ∧
      0 ≤ (3*(E.re/z.re)-E.im/z.im)/2 := by
  let f : ℝ → ℂ := fun t => z/(z^2-(t:ℂ))
  have hf : Integrable f μ := by
    simpa [f,div_eq_mul_inv] using (cauchy_kernel_integrable μ hsupp z (hT.trans hx)).const_mul z
  have hE : z*(∫ t : ℝ, (z^2-(t:ℂ))⁻¹ ∂μ) = ∫ t, f t ∂μ := by
    rw [← integral_const_mul]
    simp only [f,div_eq_mul_inv]
  dsimp only
  rw [hE]
  have hAre : Integrable (fun t => (f t).re/z.re) μ := hf.re.div_const _
  have hBim : Integrable (fun t => (f t).im/z.im) μ := hf.im.div_const _
  have hA : (∫ t, f t ∂μ).re/z.re = ∫ t, (f t).re/z.re ∂μ := by
    rw [integral_div]; exact congrArg (fun v : ℝ => v/z.re) (integral_re hf).symm
  have hB : (∫ t, f t ∂μ).im/z.im = ∫ t, (f t).im/z.im ∂μ := by
    rw [integral_div]; exact congrArg (fun v : ℝ => v/z.im) (integral_im hf).symm
  rw [hA,hB]
  have hparts : ∀ᵐ t ∂μ,
      0 ≤ (f t).re/z.re ∧ (f t).re/z.re ≤ 1/(T-t) ∧
      0 ≤ (3*((f t).re/z.re)-(f t).im/z.im)/2 := by
    filter_upwards [hsupp] with t ht
    obtain ⟨hr,hi⟩ := cauchy_root_kernel_parts z hxpos (hT.trans hx) t ht
    obtain ⟨hd,hAp,_,hCp,hAub⟩ := sextic_kernel_bounds (z.re^2) (z.im^2) t T hT hx (sq_nonneg _) ht.1 ht.2
    have hD : (z.re^2-t)^2+2*(z.re^2+t)*z.im^2+z.im^4 =
        (z.re^2-t)^2+2*(z.re^2+t)*z.im^2+(z.im^2)^2 := by ring
    dsimp only [f]
    rw [hr,hi]
    simp only [mul_div_cancel_left₀ _ hxpos.ne',neg_mul,neg_div,mul_div_cancel_left₀ _ hypos.ne']
    rw [hD]
    refine ⟨hAp,hAub,?_⟩
    convert hCp using 1 <;> ring
  refine ⟨integral_nonneg_of_ae (hparts.mono fun t ht => ht.1),
    integral_mono_ae hAre (cauchy_real_kernel_integrable μ hsupp T (by linarith))
      (hparts.mono fun t ht => ht.2.1),?_⟩
  have hpos := integral_nonneg_of_ae (hparts.mono fun t ht => ht.2.2)
  simpa only [integral_div,integral_sub (hAre.const_mul 3) hBim,integral_const_mul] using hpos

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate







theorem fifth_sextic_constant_negative (U : ℝ) (hlo : 5/2 ≤ U) (hhi : U ≤ 7/2) :
    U^3 - 5*U^2 + (70/13)*U - 98/143 < 0 := by
  have hprod := mul_nonneg (mul_nonneg (show 0 ≤ U-5/2 by linarith)
    (show 0 ≤ 7/2-U by linarith)) (show 0 ≤ U+1 by linarith)
  nlinarith only [hprod,hlo,hhi]

end DerivativeChainPrivate


set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DerivativeChainPrivate
open Polynomial MeasureTheory Set TeschlQM.Herglotz















theorem sixth_sextic_constant_negative (U : ℝ) (hlo : 5/2≤U) (hhi : U≤7/2) :
    U^3-5*U^2+(85/16)*U-1445/2184<0 := by
  have h:=fifth_sextic_constant_negative U hlo hhi
  nlinarith



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open MeasureTheory Set

theorem sixth_sextic_real_graph_negative (X : ℝ) (hlo : 5/2 ≤ X) (hhi : X ≤ 7/2) :
    ((455-3*Real.sqrt 19565)/680)*X-(559-3*Real.sqrt 19565)/688+
      (3*Real.sqrt 19565/680)*(X+(-85/43)/2-Real.sqrt (X^2+(-85/43)*X+1445/1806+(24565/211302)/X)) < 0 := by
  let H := X^2+(-85/43)*X+1445/1806+(24565/211302)/X
  let k := 3*Real.sqrt 19565/680
  let L := (91/136:ℝ)*X-13/16
  have hX : 0 < X := by linarith
  have hH : 0 < H := sixth_sextic_real_exterior X (Or.inr (by linarith))
  have hk : 0 < k := by dsimp [k]; positivity
  have hL : 0 < L := by dsimp [L]; linarith
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 19565)
  have hq := Real.sq_sqrt hH.le
  have hk2 : k^2 = 35217/92480 := by
    dsimp only [k]
    rw [div_pow,mul_pow,hs]
    norm_num
  have hid : (k*Real.sqrt H)^2-L^2 =
      -(91/1360)*(X^3-5*X^2+(85/16)*X-1445/2184)/X := by
    rw [mul_pow,hk2,hq]
    dsimp only [L,H]
    field_simp
    ring
  have hC := sixth_sextic_constant_negative X hlo hhi
  have hpos : 0 < -(91/1360:ℝ)*(X^3-5*X^2+(85/16)*X-1445/2184)/X := by exact div_pos (mul_pos_of_neg_of_neg (by norm_num) hC) hX
  have hkp : 0 < k*Real.sqrt H := mul_pos hk (Real.sqrt_pos.mpr hH)
  have hlt : L < k*Real.sqrt H := by nlinarith only [hid,hpos,hkp,hL]
  have he : ((455-3*Real.sqrt 19565)/680)*X-(559-3*Real.sqrt 19565)/688+
      (3*Real.sqrt 19565/680)*(X+(-85/43)/2-Real.sqrt (X^2+(-85/43)*X+1445/1806+(24565/211302)/X)) =
      L-k*Real.sqrt H := by dsimp [L,k,H]; ring
  rw [he]
  linarith



end DerivativeChainPrivate


set_option autoImplicit false
namespace DerivativeChainPrivate



theorem sixth_sextic_numeric_gaps :
    let s:=Real.sqrt 19565
    let αm:=(455-3*s)/680
    let αp:=(455+3*s)/680
    let bm:=(559-3*s)/688
    let bp:=(559+3*s)/688
    let k:=3*s/680
    0<k ∧ k<2/3 ∧ 1/20<αm ∧ αm<1/10 ∧
      9/10<αp ∧ bp<3/2 ∧ 1/15<41/140-bm ∧ 0<bm := by
  have hs:=Real.sq_sqrt (by norm_num : (0:ℝ)≤19565)
  have hp:=Real.sqrt_nonneg 19565
  dsimp only
  constructor <;> try nlinarith
  constructor <;> try nlinarith
  constructor <;> try nlinarith
  constructor <;> try nlinarith
  constructor <;> try nlinarith
  constructor <;> try nlinarith
  constructor <;> nlinarith


end DerivativeChainPrivate

theorem solution (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : ∀ᵐ t ∂μ, t ∈ Icc (-1/4:ℝ) (3/2))
    (hμ : ∀ u : ℂ, 0 < u.im → sexticShift (-85/43) (1445/1806) (24565/211302) u =
      TeschlQM.Herglotz.borelTransform μ u)
    (β z : ℂ) (hR : 0 ≤ β.re) (hx : 0 < z.re) (hy : 0 < z.im) (hX : 5/2 ≤ z.re^2)
    (hgraph : β/z = (((455-3*Real.sqrt 19565)/680:ℝ):ℂ)*z^2-(((559-3*Real.sqrt 19565)/688:ℝ):ℂ)+
      ((3*Real.sqrt 19565/680:ℝ):ℂ)*(∫ t : ℝ, (z^2-(t:ℂ))⁻¹ ∂μ)) : 7/2 < z.re^2 := by
  let k := 3*Real.sqrt 19565/680
  let α := (455-3*Real.sqrt 19565)/680
  let b := (559-3*Real.sqrt 19565)/688
  let E := z*(∫ t : ℝ, (z^2-(t:ℂ))⁻¹ ∂μ)
  let M := ∫ t : ℝ, 1/(z.re^2-t) ∂μ
  have hk : 0 < k := by dsimp [k]; positivity
  have hα : 0 < α := by have hh := sixth_sextic_numeric_gaps; dsimp [α]; linarith [hh.2.2.1]
  have hz : z ≠ 0 := by intro he; simp [he] at hx
  have hg : β/z = (α:ℂ)*z^2-(b:ℂ)+((k:ℂ)*E)/z := by
    convert hgraph using 1
    dsimp [α,b,k,E]
    field_simp
  have hr := (cubic_graph_coordinate_parts β z ((k:ℂ)*E) α b hz hg).1
  have hRpart : β.re/z.re = α*(z.re^2-3*z.im^2)-b+k*(E.re/z.re) := by
    rw [hr]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    field_simp
  have hA := (cauchy_root_corrections μ hsupp z hx hy (z.re^2) hX le_rfl).2.1
  change E.re/z.re ≤ M at hA
  have hM : M = z.re^2+(-85/43)/2-Real.sqrt (z.re^4+(-85/43)*z.re^2+1445/1806+(24565/211302)/z.re^2) := by
    have hb := sextic_measure_real_value (-85/43) (1445/1806) (24565/211302)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      sixth_sextic_real_exterior μ hsupp hμ (z.re^2) (by linarith)
    have ht := real_cauchy_integral_of_borel_value μ (z.re^2) _ hb
    dsimp only [M]
    convert ht using 1 <;> ring
  by_contra hn
  have hupper : z.re^2 ≤ 7/2 := le_of_not_gt hn
  have hneg := sixth_sextic_real_graph_negative (z.re^2) hX hupper
  have hnonneg : 0 ≤ β.re/z.re := div_nonneg hR hx.le
  have hyterm := mul_nonneg hα.le (sq_nonneg z.im)
  have hAM := mul_le_mul_of_nonneg_left hA hk.le
  rw [hRpart] at hnonneg
  rw [hM] at hAM
  dsimp only [α,b,k] at hnonneg hAM hyterm
  rw [show (z.re^2)^2=z.re^4 by ring] at hneg
  nlinarith only [hnonneg,hAM,hyterm,hneg]
