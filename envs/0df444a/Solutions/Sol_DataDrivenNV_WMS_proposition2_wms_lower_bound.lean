-- Prove2me | solution 1 for DataDrivenNV.WMS.proposition2_wms_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-25T02:42:08.688173+00:00
-- url     : https://prove2.me/submissions/2cac5bb9-0a69-462e-92c2-1d2bd9c47c01

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_DataDrivenNV_WMS_Setting

namespace WMSProof
open Set MeasureTheory DataDrivenNV.WMS Filter
open scoped Topology

theorem cdf_monotone (f : ℝ → ℝ) (hf : IsPdf f) : Monotone (cdfOf f) := by
  intro a b hab
  exact setIntegral_mono_set hf.2.2.1.integrableOn (ae_of_all _ hf.2.1)
    (ae_of_all _ (fun x hx => le_trans hx hab))

theorem cdf_continuous (f : ℝ → ℝ) (hf : IsPdf f) : Continuous (cdfOf f) := by
  have heq : cdfOf f = fun t => cdfOf f 0 + ∫ x in (0:ℝ)..t, f x := by
    funext t
    have h := intervalIntegral.integral_Iic_sub_Iic
      (hf.2.2.1.integrableOn (s := Iic (0:ℝ))) (hf.2.2.1.integrableOn (s := Iic t))
    unfold cdfOf
    linarith
  rw [heq]
  exact continuous_const.add (hf.2.2.1.continuous_primitive 0)

theorem cdf_atBot (f : ℝ → ℝ) : Tendsto (cdfOf f) atBot (𝓝 0) :=
  tendsto_integral_Iic_zero tendsto_id

theorem upper_mass (f : ℝ → ℝ) (hf : IsPdf f) (q : ℝ) :
    (∫ x in Ici q, f x) = 1 - cdfOf f q := by
  rw [integral_Ici_eq_integral_Ioi]
  have h := intervalIntegral.integral_Iic_add_Ioi
    (hf.2.2.1.integrableOn (s := Iic q)) (hf.2.2.1.integrableOn (s := Ioi q))
  rw [hf.2.2.2] at h
  unfold cdfOf
  linarith

theorem cdf_atTop (f : ℝ → ℝ) (hf : IsPdf f) : Tendsto (cdfOf f) atTop (𝓝 1) := by
  have ht : Tendsto (fun t : ℝ => ∫ x in Ioi t, f x) atTop (𝓝 0) :=
    tendsto_integral_Ioi_zero tendsto_id
  have heq : cdfOf f = fun t => 1 - ∫ x in Ioi t, f x := by
    funext t
    have h := upper_mass f hf t
    rw [integral_Ici_eq_integral_Ioi] at h
    linarith
  rw [heq]
  simpa using tendsto_const_nhds.sub ht

theorem quantile_mass (f : ℝ → ℝ) (hf : IsPdf f) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    cdfOf f (quantileOf f β) = β := by
  obtain ⟨a, ha⟩ := ((cdf_atBot f).eventually (gt_mem_nhds hβ0)).exists
  obtain ⟨b, hb⟩ := ((cdf_atTop f hf).eventually (lt_mem_nhds hβ1)).exists
  have hne : {q : ℝ | β ≤ cdfOf f q}.Nonempty := ⟨b, le_of_lt hb⟩
  have hbd : BddBelow {q : ℝ | β ≤ cdfOf f q} := by
    refine ⟨a, ?_⟩
    intro t ht
    by_contra hat
    have hh := cdf_monotone f hf (le_of_not_ge hat)
    exact (not_le_of_gt ha) (le_trans ht hh)
  have hclosed : IsClosed {q : ℝ | β ≤ cdfOf f q} :=
    isClosed_le continuous_const (cdf_continuous f hf)
  have hlo : β ≤ cdfOf f (quantileOf f β) := hclosed.csInf_mem hne hbd
  obtain ⟨t, ht⟩ := intermediate_value_univ a b (cdf_continuous f hf) ⟨ha.le, hb.le⟩
  have hqt : quantileOf f β ≤ t := csInf_le hbd (by simp [ht])
  have hhi := cdf_monotone f hf hqt
  rw [ht] at hhi
  exact le_antisymm hhi hlo

end WMSProof


namespace WMSProof
open Set MeasureTheory DataDrivenNV.WMS

theorem positive_support_convex (f : ℝ → ℝ)
    (hlc : ConvexOptimization.LogConcaveOn Set.univ f) :
    Convex ℝ {x : ℝ | 0 < f x} := by
  intro x hx y hy a b ha hb hab
  exact lt_of_lt_of_le (mul_pos (Real.rpow_pos_of_pos hx _) (Real.rpow_pos_of_pos hy _))
    (hlc.2 x (mem_univ x) y (mem_univ y) a b ha hb hab)

theorem log_concave_on_support (f : ℝ → ℝ)
    (hlc : ConvexOptimization.LogConcaveOn Set.univ f) :
    ConcaveOn ℝ {x : ℝ | 0 < f x} (fun x => Real.log (f x)) := by
  refine ⟨positive_support_convex f hlc, ?_⟩
  intro x hx y hy a b ha hb hab
  have hp := mul_pos (Real.rpow_pos_of_pos hx a) (Real.rpow_pos_of_pos hy b)
  have hh := hlc.2 x (mem_univ x) y (mem_univ y) a b ha hb hab
  have ht := Real.log_le_log hp hh
  simpa only [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hx a))
    (ne_of_gt (Real.rpow_pos_of_pos hy b)), Real.log_rpow hx, Real.log_rpow hy,
    smul_eq_mul] using ht

theorem exponential_envelope (f : ℝ → ℝ) (hf : IsPdf f) (q s : ℝ)
    (hq : 0 < f q) (hsg : IsLogSupergradient f q s) :
    ∀ x, f x ≤ f q * Real.exp (s * (x-q)) := by
  intro x
  by_cases hx : 0 < f x
  · have h := Real.exp_le_exp.mpr (hsg x hx)
    simpa only [Real.exp_log hx, Real.exp_add, Real.exp_log hq] using h
  · have hz : f x = 0 := le_antisymm (le_of_not_gt hx) (hf.2.1 x)
    rw [hz]
    positivity

end WMSProof

namespace WMSProof
open Set MeasureTheory DataDrivenNV.WMS

theorem supporting_slope_of_points (f : ℝ → ℝ)
    (hlc : ConvexOptimization.LogConcaveOn Set.univ f) (q a b : ℝ)
    (ha : 0 < f a) (hb : 0 < f b) (haq : a < q) (hqb : q < b) :
    ∃ s : ℝ, IsLogSupergradient f q s := by
  let S : Set ℝ := {v | ∃ x : ℝ, 0 < f x ∧ q < x ∧ v = (Real.log (f x) - Real.log (f q))/(x-q)}
  have hne : S.Nonempty := ⟨(Real.log (f b)-Real.log (f q))/(b-q), b, hb, hqb, rfl⟩
  have hc := log_concave_on_support f hlc
  have hbd : BddAbove S := by
    refine ⟨(Real.log (f q)-Real.log (f a))/(q-a), ?_⟩
    rintro v ⟨x,hx,hqx,rfl⟩
    exact hc.slope_anti_adjacent ha hx haq hqx
  refine ⟨sSup S, ?_⟩
  intro x hx
  rcases lt_trichotomy x q with h | rfl | h
  · have hs : sSup S ≤ (Real.log (f q)-Real.log (f x))/(q-x) := by
      apply csSup_le hne
      rintro v ⟨y,hy,hqy,rfl⟩
      exact hc.slope_anti_adjacent hx hy h hqy
    have hh := (le_div_iff₀ (sub_pos.mpr h)).mp hs
    nlinarith
  · simp
  · have hs : (Real.log (f x)-Real.log (f q))/(x-q) ≤ sSup S :=
      le_csSup hbd ⟨x,hx,h,rfl⟩
    have hh := (div_le_iff₀ (sub_pos.mpr h)).mp hs
    linarith

end WMSProof

namespace WMSProof
open Set MeasureTheory DataDrivenNV.WMS

theorem positive_points_of_mass (f : ℝ → ℝ) (hf : IsPdf f) (q : ℝ)
    (hq0 : 0 < cdfOf f q) (hq1 : cdfOf f q < 1) :
    (∃ a : ℝ, a < q ∧ 0 < f a) ∧ (∃ b : ℝ, q < b ∧ 0 < f b) := by
  have hl : (∫ x in Iio q, f x) ≠ 0 := by
    rw [← integral_Iic_eq_integral_Iio]
    exact ne_of_gt hq0
  have hr : (∫ x in Ioi q, f x) ≠ 0 := by
    rw [← integral_Ici_eq_integral_Ioi, upper_mass f hf q]
    exact ne_of_gt (sub_pos.mpr hq1)
  obtain ⟨a, ha, hfa⟩ := exists_ne_zero_of_setIntegral_ne_zero hl
  obtain ⟨b, hb, hfb⟩ := exists_ne_zero_of_setIntegral_ne_zero hr
  exact ⟨⟨a,ha,lt_of_le_of_ne (hf.2.1 a) (Ne.symm hfa)⟩,
    ⟨b,hb,lt_of_le_of_ne (hf.2.1 b) (Ne.symm hfb)⟩⟩

theorem positive_and_envelope_of_mass (f : ℝ → ℝ) (hf : IsPdf f)
    (hlc : ConvexOptimization.LogConcaveOn Set.univ f) (q : ℝ)
    (hq0 : 0 < cdfOf f q) (hq1 : cdfOf f q < 1) :
    0 < f q ∧ ∃ s : ℝ, ∀ x, f x ≤ f q * Real.exp (s*(x-q)) := by
  obtain ⟨⟨a,ha,hfa⟩,⟨b,hb,hfb⟩⟩ := positive_points_of_mass f hf q hq0 hq1
  have hq : 0 < f q :=
    (positive_support_convex f hlc).ordConnected.out hfa hfb ⟨ha.le,hb.le⟩
  obtain ⟨s,hs⟩ := supporting_slope_of_points f hlc q a b hfa hfb ha hb
  exact ⟨hq,s,exponential_envelope f hf q s hq hs⟩

end WMSProof

namespace WMSProof
open Set MeasureTheory DataDrivenNV.WMS

theorem exists_right_drop (f : ℝ → ℝ) (hf : IsPdf f) (q : ℝ) (hq : 0 < f q) :
    ∃ b : ℝ, q < b ∧ f b < f q := by
  by_contra h
  push Not at h
  let B := q + 2 / f q
  have hB : q < B := by dsimp [B]; linarith [div_pos (by norm_num : (0:ℝ)<2) hq]
  have hlower : f q * volume.real (Icc q B) ≤ ∫ x in Icc q B, f x := by
    apply setIntegral_ge_of_const_le_real measurableSet_Icc (measure_Icc_lt_top.ne)
      ?_ hf.2.2.1.integrableOn
    intro x hx
    rcases eq_or_lt_of_le hx.1 with rfl | hqx
    · exact le_rfl
    · exact h x hqx
  have hupper : (∫ x in Icc q B, f x) ≤ 1 := by
    simpa [hf.2.2.2] using
      (setIntegral_le_integral (s := Icc q B) hf.2.2.1 (ae_of_all _ hf.2.1))
  have hmass : f q * volume.real (Icc q B) = 2 := by
    rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hB.le)]
    dsimp [B]
    field_simp
    ring
  linarith

theorem right_exponential_or_zero (f : ℝ → ℝ) (hf : IsPdf f)
    (hlc : ConvexOptimization.LogConcaveOn Set.univ f) (q : ℝ) (hq : 0 < f q) :
    (∃ B : ℝ, ∀ x, B ≤ x → f x = 0) ∨
    (∃ B A s : ℝ, 0 < A ∧ s < 0 ∧ ∀ x, B ≤ x → f x ≤ A * Real.exp (s*x)) := by
  obtain ⟨b,hqb,hdrop⟩ := exists_right_drop f hf q hq
  by_cases hb : 0 < f b
  · right
    let s := (Real.log (f b)-Real.log (f q))/(b-q)
    have hs : s < 0 := div_neg_of_neg_of_pos
      (sub_neg.mpr (Real.log_lt_log hb hdrop)) (sub_pos.mpr hqb)
    refine ⟨b, f b * Real.exp (-s*b), s, mul_pos hb (Real.exp_pos _), hs, ?_⟩
    intro x hbx
    by_cases hx : 0 < f x
    · have hlog : Real.log (f x) ≤ Real.log (f b) + s*(x-b) := by
        rcases eq_or_lt_of_le hbx with rfl | hbx
        · simp
        · have hh := (log_concave_on_support f hlc).slope_anti_adjacent hq hx hqb hbx
          have hm := (div_le_iff₀ (sub_pos.mpr hbx)).mp hh
          dsimp [s]
          linarith
      have hh := Real.exp_le_exp.mpr hlog
      rw [Real.exp_log hx, Real.exp_add, Real.exp_log hb] at hh
      calc
        f x ≤ f b * Real.exp (s*(x-b)) := hh
        _ = f b * Real.exp (-s*b) * Real.exp (s*x) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    · have hz : f x = 0 := le_antisymm (le_of_not_gt hx) (hf.2.1 x)
      rw [hz]
      positivity
  · left
    have hb0 : f b = 0 := le_antisymm (le_of_not_gt hb) (hf.2.1 b)
    refine ⟨b, ?_⟩
    intro x hbx
    by_contra hx0
    have hx : 0 < f x := lt_of_le_of_ne (hf.2.1 x) (Ne.symm hx0)
    have : 0 < f b := (positive_support_convex f hlc).ordConnected.out hq hx ⟨hqb.le,hbx⟩
    exact (ne_of_gt this) hb0

end WMSProof

namespace WMSProof
open Set MeasureTheory DataDrivenNV.WMS

theorem right_first_moment (f : ℝ → ℝ) (hf : IsPdf f)
    (hlc : ConvexOptimization.LogConcaveOn Set.univ f) :
    IntegrableOn (fun x : ℝ => x*f x) (Ioi 0) := by
  have hn : (∫ x, f x) ≠ 0 := by rw [hf.2.2.2]; norm_num
  obtain ⟨q,hq⟩ := exists_ne_zero_of_integral_ne_zero hn
  have hqp : 0 < f q := lt_of_le_of_ne (hf.2.1 q) (Ne.symm hq)
  obtain hzero | hexp := right_exponential_or_zero f hf hlc q hqp
  · obtain ⟨b,hb⟩ := hzero
    let B := max b 0
    have hc : IntegrableOn (fun x : ℝ => x*f x) (Icc 0 B) := by
      simpa only [id_eq, mul_comm] using
        (hf.2.2.1.integrableOn (s := Icc 0 B)).mul_continuousOn continuous_id.continuousOn isCompact_Icc
    have ht : IntegrableOn (fun x : ℝ => x*f x) (Ioi B) := by
      refine (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0:ℝ)) (Ioi B)).congr_fun ?_ measurableSet_Ioi
      · intro x hx
        change 0 = x * f x
        rw [hb x (le_trans (le_max_left b 0) hx.le), mul_zero]
    exact (hc.union ht).mono_set (by intro x hx; by_cases h : x ≤ B; exact Or.inl ⟨hx.le,h⟩; exact Or.inr (lt_of_not_ge h))
  · obtain ⟨b,A,s,hA,hs,hbound⟩ := hexp
    let B := max b 0
    have hc : IntegrableOn (fun x : ℝ => x*f x) (Icc 0 B) := by
      simpa only [id_eq, mul_comm] using
        (hf.2.2.1.integrableOn (s := Icc 0 B)).mul_continuousOn continuous_id.continuousOn isCompact_Icc
    have he : IntegrableOn (fun x : ℝ => x*Real.exp (s*x)) (Ioi 0) := by
      simpa using (integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := -s)
        (by norm_num) (by norm_num) (neg_pos.mpr hs))
    have ht : IntegrableOn (fun x : ℝ => x*f x) (Ioi B) := by
      have heA : IntegrableOn (fun x : ℝ => A * (x * Real.exp (s*x))) (Ioi 0) := he.const_mul A
      have hdom := heA.mono_set (show Ioi B ⊆ Ioi 0 from fun x hx => lt_of_le_of_lt (le_max_right b 0) hx)
      apply hdom.mono' (measurable_id.mul hf.1).aestronglyMeasurable.restrict
      apply ae_restrict_of_forall_mem measurableSet_Ioi
      intro x hx
      have hx0 : 0 ≤ x := le_trans (le_max_right b 0) hx.le
      change ‖x * f x‖ ≤ A * (x * Real.exp (s*x))
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx0 (hf.2.1 x))]
      calc
        x*f x ≤ x*(A*Real.exp (s*x)) := mul_le_mul_of_nonneg_left (hbound x (le_trans (le_max_left b 0) hx.le)) hx0
        _ = A*(x*Real.exp (s*x)) := by ring
    exact (hc.union ht).mono_set (by intro x hx; by_cases h : x ≤ B; exact Or.inl ⟨hx.le,h⟩; exact Or.inr (lt_of_not_ge h))

end WMSProof

namespace WMSProof
open Set MeasureTheory DataDrivenNV.WMS

theorem reflected_pdf (f : ℝ → ℝ) (hf : IsPdf f) : IsPdf (fun x => f (-x)) := by
  refine ⟨hf.1.comp measurable_neg, fun x => hf.2.1 (-x), hf.2.2.1.comp_neg, ?_⟩
  rw [integral_neg_eq_self, hf.2.2.2]

theorem reflected_logconcave (f : ℝ → ℝ)
    (hlc : ConvexOptimization.LogConcaveOn Set.univ f) :
    ConvexOptimization.LogConcaveOn Set.univ (fun x => f (-x)) := by
  refine ⟨fun x _ => hlc.1 (-x) (mem_univ _), ?_⟩
  intro x hx y hy a b ha hb hab
  have H := hlc.2 (-x) (mem_univ _) (-y) (mem_univ _) a b ha hb hab
  have he : -(a • x + b • y) = a • (-x) + b • (-y) := by simp only [smul_eq_mul]; ring
  simpa only [he] using H

theorem first_moment (f : ℝ → ℝ) (hf : IsPdf f)
    (hlc : ConvexOptimization.LogConcaveOn Set.univ f) : Integrable (fun x : ℝ => x*f x) := by
  have hr := right_first_moment f hf hlc
  have hrg := right_first_moment (fun x => f (-x)) (reflected_pdf f hf) (reflected_logconcave f hlc)
  have hleft : IntegrableOn (fun x : ℝ => x*f x) (Iio 0) := by
    have hh : IntegrableOn (fun x : ℝ => x*f (-x)) (Ioi (- (0:ℝ))) := by simpa using hrg
    have hn := hh.comp_neg_Iio.neg
    simpa using hn
  have hclosed : IntegrableOn (fun x : ℝ => x*f x) (Iic 0) := (integrableOn_Iic_iff_integrableOn_Iio).mpr hleft
  have hu := hclosed.union hr
  simpa using hu
end WMSProof

namespace WMSProof
open MeasureTheory Set

theorem exp_mass (M s q a b : ℝ) (hs : s ≠ 0) :
    (∫ x in a..b, M * Real.exp (s*(x-q))) =
      M/s * (Real.exp (s*(b-q))-Real.exp (s*(a-q))) := by
  have hd (x : ℝ) : HasDerivAt (fun x => M/s * Real.exp (s*(x-q)))
      (M*Real.exp (s*(x-q))) x := by
    convert ((((hasDerivAt_id x).sub_const q).const_mul s).exp.const_mul (M/s)) using 1 <;>
      first | rfl | (simp only [id_eq, mul_one]; field_simp)
  have hi : IntervalIntegrable (fun x => M*Real.exp (s*(x-q))) volume a b :=
    (by fun_prop : Continuous (fun x : ℝ => M*Real.exp (s*(x-q)))).intervalIntegrable a b
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) hi]
  ring

theorem exp_moment (M s q a b : ℝ) (hs : s ≠ 0) :
    (∫ x in a..b, x * (M * Real.exp (s*(x-q)))) =
      M/s * ((b-1/s)*Real.exp (s*(b-q))-(a-1/s)*Real.exp (s*(a-q))) := by
  have hd (x : ℝ) : HasDerivAt
      (fun x => M/s * ((x-1/s)*Real.exp (s*(x-q))))
      (x*(M*Real.exp (s*(x-q)))) x := by
    convert (((hasDerivAt_id x).sub_const (1/s)).mul
      (((hasDerivAt_id x).sub_const q).const_mul s).exp).const_mul (M/s) using 1 <;>
      first | rfl | (simp only [id_eq, mul_one]; field_simp; ring)
  have hi : IntervalIntegrable (fun x => x*(M*Real.exp (s*(x-q)))) volume a b :=
    (by fun_prop : Continuous (fun x : ℝ => x*(M*Real.exp (s*(x-q))))).intervalIntegrable a b
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) hi]
  ring
end WMSProof


namespace WMSProof
open Set

noncomputable def scalarH (p x : ℝ) : ℝ :=
  (1/(1-p)+x)*Real.log (1+(1-p)*x) + (1/p-x)*Real.log (1-p*x)
noncomputable def scalarG (p x : ℝ) : ℝ := scalarH p x - min p (1-p)*x^2
noncomputable def scalarG' (p x : ℝ) : ℝ :=
  Real.log (1+(1-p)*x) - Real.log (1-p*x) - 2*min p (1-p)*x

theorem log_args_pos {p x : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hx : x ∈ Ioo (-1/(1-p)) (1/p)) : 0 < 1+(1-p)*x ∧ 0 < 1-p*x := by
  have hu : 0 < 1-p := by linarith
  have ha := (div_lt_iff₀ hu).mp hx.1
  have hb := (lt_div_iff₀ hp).mp hx.2
  constructor <;> nlinarith

theorem scalarH_deriv {p x : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hx : x ∈ Ioo (-1/(1-p)) (1/p)) :
    HasDerivAt (scalarH p) (Real.log (1+(1-p)*x)-Real.log (1-p*x)) x := by
  obtain ⟨ha,hb⟩ := log_args_pos hp hp1 hx
  have hd1 := (((hasDerivAt_const x (1/(1-p))).add (hasDerivAt_id x)).mul
    (((hasDerivAt_const x 1).add ((hasDerivAt_id x).const_mul (1-p))).log (ne_of_gt ha)))
  have hd2 := (((hasDerivAt_const x (1/p)).sub (hasDerivAt_id x)).mul
    (((hasDerivAt_const x 1).sub ((hasDerivAt_id x).const_mul p)).log (ne_of_gt hb)))
  convert hd1.add hd2 using 1 <;> first | rfl | (simp only [Pi.add_apply, Pi.sub_apply, id_eq, zero_add, zero_sub, one_mul, mul_one]; field_simp [ne_of_gt (sub_pos.mpr hp1)]; ring)

theorem scalarG_deriv {p x : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hx : x ∈ Ioo (-1/(1-p)) (1/p)) :
    HasDerivAt (scalarG p) (scalarG' p x) x := by
  convert (scalarH_deriv hp hp1 hx).sub (((hasDerivAt_id x).pow 2).const_mul (min p (1-p))) using 1 <;> first | rfl | (simp only [scalarG', id_eq, mul_one]; ring)

theorem scalarG_second {p x : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hx : x ∈ Ioo (-1/(1-p)) (1/p)) :
    HasDerivAt (scalarG' p) (1/((1+(1-p)*x)*(1-p*x))-2*min p (1-p)) x := by
  obtain ⟨ha,hb⟩ := log_args_pos hp hp1 hx
  have hd1 := ((hasDerivAt_const x 1).add ((hasDerivAt_id x).const_mul (1-p))).log (ne_of_gt ha)
  have hd2 := ((hasDerivAt_const x 1).sub ((hasDerivAt_id x).const_mul p)).log (ne_of_gt hb)
  convert (hd1.sub hd2).sub ((hasDerivAt_id x).const_mul (2*min p (1-p))) using 1 <;> first | rfl | (simp only [Pi.add_apply, Pi.sub_apply, id_eq, zero_add, zero_sub, mul_one]; field_simp [ne_of_gt (sub_pos.mpr hp1)]; ring)

theorem scalar_second_nonneg {p x : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hx : x ∈ Ioo (-1/(1-p)) (1/p)) :
    0 ≤ 1/((1+(1-p)*x)*(1-p*x))-2*min p (1-p) := by
  obtain ⟨ha,hb⟩ := log_args_pos hp hp1 hx
  have hD : 0 < (1+(1-p)*x)*(1-p*x) := mul_pos ha hb
  have hsq := sq_nonneg (2*p*(1-p)*x-((1-p)-p))
  have hbound : 4*p*(1-p) ≤ 1/((1+(1-p)*x)*(1-p*x)) := by
    apply (le_div_iff₀ hD).2
    nlinarith
  have hmin : 2*min p (1-p) ≤ 4*p*(1-p) := by
    rcases le_total p (1-p) with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]; nlinarith
  linarith


theorem scalar_bound {p x : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hx : x ∈ Ioo (-1/(1-p)) (1/p)) :
    min p (1-p)*x^2 ≤ scalarH p x := by
  have hz : (0:ℝ) ∈ Ioo (-1/(1-p)) (1/p) := by
    constructor
    · exact div_neg_of_neg_of_pos (by norm_num) (sub_pos.mpr hp1)
    · exact one_div_pos.mpr hp
  have hc : ConvexOn ℝ (Ioo (-1/(1-p)) (1/p)) (scalarG p) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioo _ _)
      (fun y hy => (scalarG_deriv hp hp1 hy).continuousAt.continuousWithinAt)
      (fun y hy => (scalarG_deriv hp hp1 (interior_subset hy)).hasDerivWithinAt)
      (fun y hy => (scalarG_second hp hp1 (interior_subset hy)).hasDerivWithinAt)
      (fun y hy => scalar_second_nonneg hp hp1 (interior_subset hy))
  have hd0 : HasDerivAt (scalarG p) 0 0 := by
    simpa [scalarG'] using scalarG_deriv hp hp1 hz
  have hg0 : scalarG p 0 = 0 := by simp [scalarG, scalarH]
  have hg : 0 ≤ scalarG p x := by
    rcases lt_trichotomy 0 x with h | h | h
    · have hh := hc.le_slope_of_hasDerivAt hz hx h hd0
      rw [slope_def_field, hg0, sub_zero, sub_zero] at hh
      simpa using (le_div_iff₀ h).mp hh
    · subst x; simp [hg0]
    · have hh := hc.slope_le_of_hasDerivAt hx hz h hd0
      rw [slope_def_field, hg0, zero_sub, zero_sub] at hh
      have hn : 0 < -x := by linarith
      have := (div_le_iff₀ hn).mp hh
      linarith
  dsimp [scalarG] at hg
  linarith

end WMSProof

namespace WMSProof
open MeasureTheory Set

noncomputable def lowerEnd (M s q p : ℝ) := q + Real.log (1-s*p/M)/s
noncomputable def upperEnd (M s q p : ℝ) := q + Real.log (1+s*(1-p)/M)/s

theorem endpoint_args {M s p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ha : s/M ∈ Ioo (-1/(1-p)) (1/p)) :
    0 < 1-s*p/M ∧ 0 < 1+s*(1-p)/M := by
  have H := log_args_pos hp hp1 ha
  constructor
  · convert H.2 using 1; ring
  · convert H.1 using 1; ring

theorem lower_exp {M s q p : ℝ} (hs : s ≠ 0) (hA : 0 < 1-s*p/M) :
    Real.exp (s*(lowerEnd M s q p-q)) = 1-s*p/M := by
  have he : s*(lowerEnd M s q p-q) = Real.log (1-s*p/M) := by
    dsimp [lowerEnd]; field_simp; ring
  rw [he, Real.exp_log hA]

theorem upper_exp {M s q p : ℝ} (hs : s ≠ 0) (hB : 0 < 1+s*(1-p)/M) :
    Real.exp (s*(upperEnd M s q p-q)) = 1+s*(1-p)/M := by
  have he : s*(upperEnd M s q p-q) = Real.log (1+s*(1-p)/M) := by
    dsimp [upperEnd]; field_simp; ring
  rw [he, Real.exp_log hB]

theorem lower_le {M s q p : ℝ} (hM : 0 < M) (hp : 0 < p)
    (hs : s ≠ 0) (hA : 0 < 1-s*p/M) : lowerEnd M s q p ≤ q := by
  dsimp [lowerEnd]
  suffices Real.log (1-s*p/M)/s ≤ 0 by linarith
  rcases lt_or_gt_of_ne hs with hs | hs
  · apply div_nonpos_of_nonneg_of_nonpos
    · apply Real.log_nonneg
      have : s*p/M ≤ 0 := div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hs.le hp.le) hM.le
      linarith
    · exact hs.le
  · apply div_nonpos_of_nonpos_of_nonneg
    · apply Real.log_nonpos hA.le
      have : 0 ≤ s*p/M := le_of_lt (div_pos (mul_pos hs hp) hM)
      linarith
    · exact hs.le

theorem upper_ge {M s q p : ℝ} (hM : 0 < M) (hp1 : p < 1)
    (hs : s ≠ 0) (hB : 0 < 1+s*(1-p)/M) : q ≤ upperEnd M s q p := by
  dsimp [upperEnd]
  suffices 0 ≤ Real.log (1+s*(1-p)/M)/s by linarith
  rcases lt_or_gt_of_ne hs with hs | hs
  · apply div_nonneg_of_nonpos
    · apply Real.log_nonpos hB.le
      have : s*(1-p)/M ≤ 0 := div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hs.le (sub_nonneg.mpr hp1.le)) hM.le
      linarith
    · exact hs.le
  · apply div_nonneg
    · apply Real.log_nonneg
      have : 0 ≤ s*(1-p)/M := le_of_lt (div_pos (mul_pos hs (sub_pos.mpr hp1)) hM)
      linarith
    · exact hs.le

theorem exp_lower_mass {M s q p : ℝ} (hM : 0 < M) (hs : s ≠ 0)
    (hA : 0 < 1-s*p/M) :
    (∫ x in lowerEnd M s q p..q, M*Real.exp (s*(x-q))) = p := by
  rw [exp_mass _ _ _ _ _ hs, lower_exp hs hA]
  simp only [sub_self, mul_zero, Real.exp_zero]
  field_simp
  ring

theorem exp_upper_mass {M s q p : ℝ} (hM : 0 < M) (hs : s ≠ 0)
    (hB : 0 < 1+s*(1-p)/M) :
    (∫ x in q..upperEnd M s q p, M*Real.exp (s*(x-q))) = 1-p := by
  rw [exp_mass _ _ _ _ _ hs, upper_exp hs hB]
  simp only [sub_self, mul_zero, Real.exp_zero]
  field_simp
  ring

end WMSProof


namespace WMSProof
open MeasureTheory Set
open DataDrivenNV.WMS

theorem moment_le_of_crossing {f g : ℝ → ℝ} {S : Set ℝ} {a : ℝ}
    (hS : MeasurableSet S) (hf : IntegrableOn f S) (hg : IntegrableOn g S)
    (hxf : IntegrableOn (fun x => x * f x) S)
    (hxg : IntegrableOn (fun x => x * g x) S)
    (hm : (∫ x in S, f x) = ∫ x in S, g x)
    (hc : ∀ x ∈ S, (x-a)*(f x-g x) ≤ 0) :
    (∫ x in S, x*f x) ≤ ∫ x in S, x*g x := by
  have hz : (∫ x in S, (x-a)*(f x-g x)) ≤ 0 :=
    integral_nonpos_of_ae (ae_restrict_of_forall_mem hS (fun x hx => hc x hx))
  have he : (fun x => (x-a)*(f x-g x)) =
      (fun x => (x*f x-x*g x)-a*(f x-g x)) := by funext x; ring
  rw [he] at hz
  change (∫ x in S, ((fun x => x*f x) - (fun x => x*g x)) x -
      a*(f-g) x) ≤ 0 at hz
  rw [integral_sub (hxf.sub hxg) ((hf.sub hg).const_mul a)] at hz
  simp only [Pi.sub_apply] at hz
  rw [integral_sub hxf hxg, integral_const_mul, integral_sub hf hg, hm] at hz
  linarith

theorem moment_ge_of_crossing {f g : ℝ → ℝ} {S : Set ℝ} {a : ℝ}
    (hS : MeasurableSet S) (hf : IntegrableOn f S) (hg : IntegrableOn g S)
    (hxf : IntegrableOn (fun x => x * f x) S)
    (hxg : IntegrableOn (fun x => x * g x) S)
    (hm : (∫ x in S, f x) = ∫ x in S, g x)
    (hc : ∀ x ∈ S, 0 ≤ (x-a)*(f x-g x)) :
    (∫ x in S, x*g x) ≤ ∫ x in S, x*f x := by
  apply moment_le_of_crossing hS hg hf hxg hxf hm.symm
  intro x hx
  have := hc x hx
  nlinarith

end WMSProof

namespace WMSProof
open MeasureTheory Set

noncomputable def clip (a b : ℝ) (h : ℝ → ℝ) := (Icc a b).indicator h

theorem clip_integrable {a b : ℝ} {h : ℝ → ℝ} (hh : Continuous h) :
    Integrable (clip a b h) :=
  hh.continuousOn.integrableOn_Icc.integrable_indicator measurableSet_Icc

theorem clip_moment (a b : ℝ) (h : ℝ → ℝ) :
    (fun x => x * clip a b h x) = clip a b (fun x => x*h x) := by
  funext x
  by_cases hx : x ∈ Icc a b <;> simp [clip, hx]

theorem clip_right_integral {q b : ℝ} (hqb : q ≤ b) (h : ℝ → ℝ) :
    (∫ x in Ici q, clip q b h x) = ∫ x in q..b, h x := by
  rw [clip, setIntegral_indicator measurableSet_Icc]
  have he : Ici q ∩ Icc q b = Icc q b := by ext x; simp
  rw [he, integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hqb]

theorem clip_left_integral {a q : ℝ} (haq : a ≤ q) (h : ℝ → ℝ) :
    (∫ x in Iic q, clip a q h x) = ∫ x in a..q, h x := by
  rw [clip, setIntegral_indicator measurableSet_Icc]
  have he : Iic q ∩ Icc a q = Icc a q := by ext x; simp
  rw [he, integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le haq]

theorem right_moment_lower {f h : ℝ → ℝ} {q b : ℝ}
    (hf : Integrable f) (hxf : Integrable (fun x => x*f x))
    (hn : ∀ x, 0 ≤ f x) (hh : Continuous h) (hcap : ∀ x, f x ≤ h x)
    (hqb : q ≤ b) (hm : (∫ x in Ici q, f x) = ∫ x in q..b, h x) :
    (∫ x in q..b, x*h x) ≤ ∫ x in Ici q, x*f x := by
  have hg := clip_integrable (a := q) (b := b) hh
  have hxg : Integrable (fun x => x*clip q b h x) := by
    rw [clip_moment]
    exact clip_integrable (continuous_id.mul hh)
  have he := moment_ge_of_crossing (a := b) measurableSet_Ici hf.integrableOn
    hg.integrableOn hxf.integrableOn hxg.integrableOn
    (hm.trans (clip_right_integral hqb h).symm) (by
      intro x hx
      by_cases hxb : x ≤ b
      · have hx' : x ∈ Icc q b := ⟨hx, hxb⟩
        simp only [clip, indicator_of_mem hx']
        exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hxb) (sub_nonpos.mpr (hcap x))
      · have hx' : x ∉ Icc q b := fun H => hxb H.2
        simp only [clip, indicator_of_notMem hx', sub_zero]
        exact mul_nonneg (sub_nonneg.mpr (le_of_not_ge hxb)) (hn x))
  rw [clip_moment, clip_right_integral hqb] at he
  exact he

theorem left_moment_upper {f h : ℝ → ℝ} {a q : ℝ}
    (hf : Integrable f) (hxf : Integrable (fun x => x*f x))
    (hn : ∀ x, 0 ≤ f x) (hh : Continuous h) (hcap : ∀ x, f x ≤ h x)
    (haq : a ≤ q) (hm : (∫ x in Iic q, f x) = ∫ x in a..q, h x) :
    (∫ x in Iic q, x*f x) ≤ ∫ x in a..q, x*h x := by
  have hg := clip_integrable (a := a) (b := q) hh
  have hxg : Integrable (fun x => x*clip a q h x) := by
    rw [clip_moment]
    exact clip_integrable (continuous_id.mul hh)
  have he := moment_le_of_crossing (a := a) measurableSet_Iic hf.integrableOn
    hg.integrableOn hxf.integrableOn hxg.integrableOn
    (hm.trans (clip_left_integral haq h).symm) (by
      intro x hx
      by_cases hax : a ≤ x
      · have hx' : x ∈ Icc a q := ⟨hax, hx⟩
        simp only [clip, indicator_of_mem hx']
        exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hax) (sub_nonpos.mpr (hcap x))
      · have hx' : x ∉ Icc a q := fun H => hax H.1
        simp only [clip, indicator_of_notMem hx', sub_zero]
        exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_ge hax)) (hn x))
  rw [clip_moment, clip_left_integral haq] at he
  exact he

end WMSProof

namespace WMSProof
open MeasureTheory Set
open DataDrivenNV.WMS

theorem scaled_exp_spread {M s q p : ℝ} (hM : 0 < M) (hs : s ≠ 0)
    (hp : 0 < p) (hp1 : p < 1)
    (ha : s/M ∈ Ioo (-1/(1-p)) (1/p)) :
    M * ((∫ x in q..upperEnd M s q p, x*(M*Real.exp (s*(x-q))))/(1-p) -
      (∫ x in lowerEnd M s q p..q, x*(M*Real.exp (s*(x-q))))/p) =
      scalarH p (s/M)/(s/M)^2 := by
  obtain ⟨hA,hB⟩ := endpoint_args hp hp1 ha
  rw [exp_moment _ _ _ _ _ hs, exp_moment _ _ _ _ _ hs,
    upper_exp hs hB, lower_exp hs hA]
  simp only [sub_self, mul_zero, Real.exp_zero, mul_one]
  have hlogA : Real.log (1-p*(s/M)) = Real.log (1-s*p/M) := by congr 1; ring
  have hlogB : Real.log (1+(1-p)*(s/M)) = Real.log (1+s*(1-p)/M) := by congr 1; ring
  dsimp [scalarH, lowerEnd, upperEnd]
  rw [hlogA,hlogB]
  field_simp [ne_of_gt (sub_pos.mpr hp1)]
  ring

theorem exp_envelope_bound {f : ℝ → ℝ} {q p M s : ℝ}
    (hf : IsPdf f) (hxf : Integrable (fun x => x*f x))
    (hp : 0 < p) (hp1 : p < 1) (hM : 0 < M) (hs : s ≠ 0)
    (hl : (∫ x in Iic q, f x) = p) (hr : (∫ x in Ici q, f x) = 1-p)
    (ha : s/M ∈ Ioo (-1/(1-p)) (1/p))
    (hcap : ∀ x, f x ≤ M*Real.exp (s*(x-q))) :
    min p (1-p) ≤ ams f q*M := by
  obtain ⟨hA,hB⟩ := endpoint_args hp hp1 ha
  have hcont : Continuous (fun x : ℝ => M*Real.exp (s*(x-q))) := by fun_prop
  have L := left_moment_upper hf.2.2.1 hxf hf.2.1 hcont hcap
    (lower_le hM hp hs hA) (hl.trans (exp_lower_mass hM hs hA).symm)
  have R := right_moment_lower hf.2.2.1 hxf hf.2.1 hcont hcap
    (upper_ge hM hp1 hs hB) (hr.trans (exp_upper_mass hM hs hB).symm)
  have hdiv := sub_le_sub (div_le_div_of_nonneg_right R (sub_nonneg.mpr hp1.le))
    (div_le_div_of_nonneg_right L hp.le)
  have H := mul_le_mul_of_nonneg_left hdiv hM.le
  rw [scaled_exp_spread hM hs hp hp1 ha] at H
  have hsq : 0 < (s/M)^2 := sq_pos_of_ne_zero (div_ne_zero hs (ne_of_gt hM))
  have hscl : min p (1-p) ≤ scalarH p (s/M)/(s/M)^2 :=
    (le_div_iff₀ hsq).mpr (scalar_bound hp hp1 ha)
  change cdfOf f q = p at hl
  dsimp [ams]
  rw [hl, mul_comm]
  exact hscl.trans H

end WMSProof

namespace WMSProof
open MeasureTheory Set
open DataDrivenNV.WMS

theorem uniform_mass (M a b : ℝ) : (∫ _x in a..b, M) = (b-a)*M := by
  simp [intervalIntegral.integral_const, smul_eq_mul]

theorem uniform_moment (M a b : ℝ) :
    (∫ x in a..b, x*M) = M/2*(b^2-a^2) := by
  have hd (x : ℝ) : HasDerivAt (fun x => M/2*x^2) (x*M) x := by
    convert ((hasDerivAt_id x).pow 2).const_mul (M/2) using 1 <;>
      first | rfl | (simp only [id_eq, mul_one]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    ((continuous_id.mul continuous_const).intervalIntegrable a b)]
  ring

theorem uniform_bound {f : ℝ → ℝ} {q p M : ℝ}
    (hf : IsPdf f) (hxf : Integrable (fun x => x*f x))
    (hp : 0 < p) (hp1 : p < 1) (hM : 0 < M)
    (hl : (∫ x in Iic q, f x) = p) (hr : (∫ x in Ici q, f x) = 1-p)
    (hcap : ∀ x, f x ≤ M) :
    min p (1-p) ≤ ams f q*M := by
  have ha : q-p/M ≤ q := sub_le_self _ (div_nonneg hp.le hM.le)
  have hb : q ≤ q+(1-p)/M := le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr hp1.le) hM.le)
  have hml : (∫ x in Iic q, f x) = ∫ _x in (q-p/M)..q, M := by
    rw [hl, uniform_mass]; field_simp; ring
  have hmr : (∫ x in Ici q, f x) = ∫ _x in q..(q+(1-p)/M), M := by
    rw [hr, uniform_mass]; field_simp; ring
  have L := left_moment_upper hf.2.2.1 hxf hf.2.1 continuous_const hcap ha hml
  have R := right_moment_lower hf.2.2.1 hxf hf.2.1 continuous_const hcap hb hmr
  rw [uniform_moment] at L R
  have hm : min p (1-p) ≤ 1/2 := by
    have := min_le_left p (1-p)
    have := min_le_right p (1-p)
    linarith
  have hdiv := sub_le_sub (div_le_div_of_nonneg_right R (sub_nonneg.mpr hp1.le))
    (div_le_div_of_nonneg_right L hp.le)
  have he : (M/2*((q+(1-p)/M)^2-q^2))/(1-p) -
      (M/2*(q^2-(q-p/M)^2))/p = 1/(2*M) := by
    field_simp [ne_of_gt (sub_pos.mpr hp1)]; ring
  rw [he] at hdiv
  have H := mul_le_mul_of_nonneg_right hdiv hM.le
  have he' : 1/(2*M)*M = (1:ℝ)/2 := by field_simp
  rw [he'] at H
  change min p (1-p) ≤ ((∫ x in Ici q, x*f x)/(1-cdfOf f q)-
    (∫ x in Iic q, x*f x)/cdfOf f q)*M
  change cdfOf f q = p at hl
  rw [hl]
  exact hm.trans H
end WMSProof

namespace WMSProof

theorem bound_at_height {L A c : ℝ} (hc : 0 < c) (hL : 0 < L)
    (h : ∀ M : ℝ, c < M → L ≤ A*M) : L ≤ A*c := by
  have h1 := h (c+1) (by linarith)
  have hA : 0 < A := by nlinarith
  by_contra H
  have hh : A*c < L := lt_of_not_ge H
  have hcm : c < (L/A+c)/2 := by
    have : c < L/A := (lt_div_iff₀ hA).mpr (by nlinarith)
    linarith
  have h2 := h ((L/A+c)/2) hcm
  have he : A*(L/A) = L := by field_simp
  nlinarith

theorem inflated_slope {p c s M : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hc : 0 < c) (hM : c < M)
    (hs : -c/(1-p) ≤ s ∧ s ≤ c/p) :
    s/M ∈ Set.Ioo (-1/(1-p)) (1/p) := by
  have hMp : 0 < M := lt_trans hc hM
  have hu : 0 < 1-p := sub_pos.mpr hp1
  constructor
  · apply (lt_div_iff₀ hMp).mpr
    have H := (div_le_iff₀ hu).mp hs.1
    have he : -1/(1-p)*M = -M/(1-p) := by ring
    rw [he]
    apply (div_lt_iff₀ hu).mpr
    linarith
  · apply (div_lt_iff₀ hMp).mpr
    have H := (le_div_iff₀ hp).mp hs.2
    have he : 1/p*M = M/p := by ring
    rw [he]
    apply (lt_div_iff₀ hp).mpr
    linarith

end WMSProof

namespace WMSProof
open Set MeasureTheory DataDrivenNV.WMS

theorem envelope_slope_bounds {f : ℝ → ℝ} {q p c s : ℝ}
    (hf : IsPdf f) (hp : 0<p) (hp1 : p<1) (hc : 0<c)
    (hl : cdfOf f q=p) (hcap : ∀x,f x≤c*Real.exp (s*(x-q))) :
    -c/(1-p) ≤ s ∧ s ≤ c/p := by
  have hform : (fun x : ℝ => c*Real.exp (s*(x-q))) =
      (fun x => (c*Real.exp (-s*q))*Real.exp (s*x)) := by
    funext x
    rw [mul_assoc, ← Real.exp_add]
    congr 2; ring
  have hcancel : Real.exp (-s*q) * Real.exp (s*q) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  constructor
  · by_cases hs : s < 0
    · have hi : IntegrableOn (fun x : ℝ => c*Real.exp (s*(x-q))) (Ioi q) := by
        rw [hform]; exact (integrableOn_exp_mul_Ioi hs q).const_mul _
      have hm := setIntegral_mono_on hf.2.2.1.integrableOn hi measurableSet_Ioi (fun x _ => hcap x)
      have hv : (∫ x in Ioi q, c*Real.exp (s*(x-q))) = -c/s := by
        rw [hform, integral_const_mul, integral_exp_mul_Ioi hs q]
        calc
          c*Real.exp (-s*q)*(-Real.exp (s*q)/s) = -c*(Real.exp (-s*q)*Real.exp (s*q))/s := by ring
          _ = -c/s := by rw [hcancel]; ring
      have hu : (∫ x in Ioi q, f x) = 1-p := by
        rw [← integral_Ici_eq_integral_Ioi, upper_mass f hf q, hl]
      rw [hv, hu] at hm
      have hmul := (le_div_iff_of_neg hs).mp hm
      exact (div_le_iff₀ (sub_pos.mpr hp1)).mpr (by nlinarith)
    · exact le_trans (div_nonpos_of_nonpos_of_nonneg (by linarith : -c ≤ 0) (sub_pos.mpr hp1).le) (le_of_not_gt hs)
  · by_cases hs : 0 < s
    · have hi : IntegrableOn (fun x : ℝ => c*Real.exp (s*(x-q))) (Iic q) := by
        rw [hform]; exact (integrableOn_exp_mul_Iic hs q).const_mul _
      have hm := setIntegral_mono_on hf.2.2.1.integrableOn hi measurableSet_Iic (fun x _ => hcap x)
      have hv : (∫ x in Iic q, c*Real.exp (s*(x-q))) = c/s := by
        rw [hform, integral_const_mul, integral_exp_mul_Iic hs q]
        calc
          c*Real.exp (-s*q)*(Real.exp (s*q)/s) = c*(Real.exp (-s*q)*Real.exp (s*q))/s := by ring
          _ = c/s := by rw [hcancel]; ring
      change cdfOf f q ≤ _ at hm
      rw [hl, hv] at hm
      exact (le_div_iff₀ hp).mpr (by nlinarith [(le_div_iff₀ hs).mp hm])
    · exact le_trans (le_of_not_gt hs) (div_pos hc hp).le
end WMSProof

namespace WMSProof
open MeasureTheory Set
open DataDrivenNV.WMS

theorem bound_of_envelope {f : ℝ → ℝ} {q p c s : ℝ}
    (hf : IsPdf f) (hxf : Integrable (fun x => x*f x))
    (hl : cdfOf f q = p) (hp : 0 < p) (hp1 : p < 1)
    (hc : 0 < c) (hcq : c = f q)
    (hcap : ∀ x, f x ≤ c*Real.exp (s*(x-q))) :
    min p (1-p) ≤ ams f q*c := by
  rcases hcq with rfl
  have hr : (∫ x in Ici q, f x) = 1-p := by rw [upper_mass f hf q, hl]
  have hlow : (∫ x in Iic q, f x) = p := hl
  apply bound_at_height hc (lt_min hp (sub_pos.mpr hp1))
  intro M hM
  have hMp : 0 < M := lt_trans hc hM
  have hcapM : ∀ x, f x ≤ M*Real.exp (s*(x-q)) := by
    intro x
    exact (hcap x).trans (mul_le_mul_of_nonneg_right hM.le (Real.exp_pos _).le)
  by_cases hs : s = 0
  · apply uniform_bound hf hxf hp hp1 hMp hlow hr
    intro x
    simpa [hs] using hcapM x
  · exact exp_envelope_bound hf hxf hp hp1 hMp hs hlow hr
      (inflated_slope hp hp1 hc hM (envelope_slope_bounds hf hp hp1 hc hl hcap)) hcapM

end WMSProof

namespace WMSProof
open Set MeasureTheory DataDrivenNV.WMS

theorem full_solution (b h : ℝ) (hb : 0 < b) (hh : 0 < h)
    (f : ℝ → ℝ) (hf : IsPdf f)
    (hlc : ConvexOptimization.LogConcaveOn Set.univ f) :
    min b h / (b+h) ≤ ams f (quantileOf f (b/(b+h))) * f (quantileOf f (b/(b+h))) := by
  have hsum : 0 < b+h := add_pos hb hh
  have hp : 0 < b/(b+h) := div_pos hb hsum
  have hp1 : b/(b+h) < 1 := (div_lt_one hsum).mpr (by linarith)
  have hmass := quantile_mass f hf (b/(b+h)) hp hp1
  obtain ⟨hc,s,hcap⟩ := positive_and_envelope_of_mass f hf hlc (quantileOf f (b/(b+h)))
    (by rw [hmass]; exact hp) (by rw [hmass]; exact hp1)
  have H := bound_of_envelope hf (first_moment f hf hlc) hmass hp hp1 hc rfl hcap
  have hsub : 1-b/(b+h) = h/(b+h) := by field_simp; ring
  rw [hsub] at H
  simpa only [min_div_div_right hsum.le] using H
end WMSProof

namespace DataDrivenNV.WMS
theorem proposition2_wms_lower_bound (b h : ℝ) (hb : 0 < b) (hh : 0 < h)
    (f : ℝ → ℝ) (hf : IsPdf f) (hlc : ConvexOptimization.LogConcaveOn Set.univ f) :
    min b h / (b + h) ≤
      ams f (quantileOf f (b / (b + h))) * f (quantileOf f (b / (b + h))) := WMSProof.full_solution b h hb hh f hf hlc
end DataDrivenNV.WMS

open DataDrivenNV.WMS
theorem solution (b h : ℝ) (hb : 0 < b) (hh : 0 < h)
    (f : ℝ → ℝ) (hf : IsPdf f) (hlc : ConvexOptimization.LogConcaveOn Set.univ f) :
    min b h / (b + h) ≤
      ams f (quantileOf f (b / (b + h))) * f (quantileOf f (b / (b + h))) := WMSProof.full_solution b h hb hh f hf hlc
