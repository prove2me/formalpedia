-- Prove2me | solution 1 for ExploreFirst.Absolute.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:40:56.805001+00:00
-- url     : https://prove2.me/submissions/43da1e49-55e9-44b4-adab-9e1cd7898379

import Mathlib
import Definitions.Def_ExploreFirst_FundIneq_Setting

set_option autoImplicit false
open MeasureTheory InformationTheory ProbabilityTheory ExploreFirst.FundIneq

lemma bern_prob (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : IsProbabilityMeasure (bernoulliLaw p) := by
  constructor
  unfold bernoulliLaw
  simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one,
    Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, Measure.dirac_apply_of_mem,
    Set.mem_univ, ENNReal.smul_def]
  rw [← ENNReal.ofReal_add h0 (by linarith)]
  simp

noncomputable def dens2 (p q : ℝ) : ℝ → ENNReal := fun x =>
  if x = 1 then ENNReal.ofReal (p / q) else ENNReal.ofReal ((1 - p) / (1 - q))

lemma dens2_meas (p q : ℝ) : Measurable (dens2 p q) := by
  unfold dens2
  exact Measurable.ite (measurableSet_singleton _) measurable_const measurable_const

lemma bern_density (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 < q) (hq1 : q < 1) :
    bernoulliLaw p = (bernoulliLaw q).withDensity (dens2 p q) := by
  ext s hs
  rw [withDensity_apply _ hs, ← lintegral_indicator hs]
  have hm : Measurable (s.indicator (dens2 p q)) := (dens2_meas p q).indicator hs
  have e1 : ∫⁻ x, s.indicator (dens2 p q) x ∂(bernoulliLaw q) =
      ENNReal.ofReal q * s.indicator (dens2 p q) 1 +
        ENNReal.ofReal (1 - q) * s.indicator (dens2 p q) 0 := by
    unfold bernoulliLaw
    rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
      lintegral_dirac' _ hm, lintegral_dirac' _ hm]
    simp [ENNReal.smul_def]
  rw [e1]
  unfold bernoulliLaw
  simp only [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ hs, ENNReal.smul_def,
    smul_eq_mul]
  have g1 : dens2 p q 1 = ENNReal.ofReal (p / q) := by simp [dens2]
  have g2 : dens2 p q 0 = ENNReal.ofReal ((1 - p) / (1 - q)) := by
    simp only [dens2]; rw [if_neg]; norm_num
  have k1 : ENNReal.ofReal q * ENNReal.ofReal (p / q) = ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_mul hq0.le]
    congr 1; field_simp
  have k2 : ENNReal.ofReal (1 - q) * ENNReal.ofReal ((1 - p) / (1 - q)) =
      ENNReal.ofReal (1 - p) := by
    rw [← ENNReal.ofReal_mul (by linarith)]
    have : (1 - q) ≠ 0 := (by linarith : (0:ℝ) < 1 - q).ne'
    congr 1; field_simp
  classical
  by_cases h1 : (1 : ℝ) ∈ s <;> by_cases h2 : (0 : ℝ) ∈ s <;>
    simp only [Set.indicator_apply, Pi.one_apply, h1, h2, if_true, if_false, g1, g2, k1, k2,
      mul_one, mul_zero, add_zero, zero_add]

lemma kl_bern (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 < q) (hq1 : q < 1) :
    klBer p q =
      ENNReal.ofReal (p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))) := by
  unfold klBer
  haveI := bern_prob p hp0 hp1
  haveI := bern_prob q hq0.le hq1.le
  have hd := bern_density p q hp0 hp1 hq0 hq1
  have hac : bernoulliLaw p ≪ bernoulliLaw q := by
    rw [hd]; exact withDensity_absolutelyContinuous _ _
  have hrn : ∀ᵐ x ∂(bernoulliLaw p), (bernoulliLaw p).rnDeriv (bernoulliLaw q) x = dens2 p q x := by
    have := Measure.rnDeriv_withDensity (bernoulliLaw q) (dens2_meas p q)
    rw [← hd] at this
    exact hac.ae_le this
  set h : ℝ → ℝ := fun x => Real.log (dens2 p q x).toReal with hh
  have hbound : ∀ x, ‖h x‖ ≤ |Real.log (p / q)| + |Real.log ((1 - p) / (1 - q))| := by
    intro x
    simp only [hh, dens2]
    split_ifs
    · rw [ENNReal.toReal_ofReal (div_nonneg hp0 hq0.le), Real.norm_eq_abs]; linarith [abs_nonneg (Real.log ((1 - p) / (1 - q)))]
    · rw [ENNReal.toReal_ofReal (div_nonneg (by linarith) (by linarith)), Real.norm_eq_abs]
      linarith [abs_nonneg (Real.log (p / q))]
  have hhm : Measurable h := by
    show Measurable (fun x => Real.log (dens2 p q x).toReal)
    exact (Measurable.log (ENNReal.measurable_toReal.comp (dens2_meas p q)))
  have hint : Integrable h (bernoulliLaw p) :=
    Integrable.of_bound hhm.aestronglyMeasurable _ (ae_of_all _ hbound)
  have hllr : llr (bernoulliLaw p) (bernoulliLaw q) =ᵐ[bernoulliLaw p] h := by
    filter_upwards [hrn] with x hx
    simp [llr, hx, hh]
  have hint2 : Integrable (llr (bernoulliLaw p) (bernoulliLaw q)) (bernoulliLaw p) :=
    hint.congr hllr.symm
  rw [klDiv_of_ac_of_integrable hac hint2, integral_congr_ae hllr]
  have hI : ∫ x, h x ∂(bernoulliLaw p) = p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q)) := by
    unfold bernoulliLaw
    haveI : IsFiniteMeasure (ENNReal.ofReal p • Measure.dirac (1 : ℝ)) := ⟨by simp⟩
    haveI : IsFiniteMeasure (ENNReal.ofReal (1 - p) • Measure.dirac (0 : ℝ)) := ⟨by simp⟩
    have i1 : Integrable h (ENNReal.ofReal p • Measure.dirac (1 : ℝ)) :=
      Integrable.of_bound hhm.aestronglyMeasurable _ (ae_of_all _ hbound)
    have i2 : Integrable h (ENNReal.ofReal (1 - p) • Measure.dirac (0 : ℝ)) :=
      Integrable.of_bound hhm.aestronglyMeasurable _ (ae_of_all _ hbound)
    rw [integral_add_measure i1 i2, integral_smul_measure, integral_smul_measure,
      integral_dirac, integral_dirac]
    have g1 : h 1 = Real.log (p / q) := by simp [hh, dens2, ENNReal.toReal_ofReal (div_nonneg hp0 hq0.le)]
    have g2 : h 0 = Real.log ((1 - p) / (1 - q)) := by
      simp only [hh, dens2]; rw [if_neg (by norm_num), ENNReal.toReal_ofReal (div_nonneg (by linarith) (by linarith))]
    rw [g1, g2]
    simp [ENNReal.toReal_ofReal hp0, ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ 1 - p)]
  rw [hI]
  simp

lemma kl_bern_one (p : ℝ) (hp1 : p < 1) : klBer p 1 = ⊤ := by
  unfold klBer
  apply klDiv_of_not_ac
  intro hac
  have h1 : bernoulliLaw 1 {0} = 0 := by
    simp [bernoulliLaw]
  have h2 := hac h1
  have h3 : bernoulliLaw p {0} = ENNReal.ofReal (1 - p) := by
    simp [bernoulliLaw]
  rw [h3] at h2
  have : 0 < ENNReal.ofReal (1 - p) := ENNReal.ofReal_pos.mpr (by linarith)
  exact this.ne' h2

/-- the real inequality -/
lemma kl_real (p q V : ℝ) (hp : 0 ≤ p) (hpq : p < q) (hq : q < 1) (hV : 0 < V)
    (hVb : ∀ x ∈ Set.Icc p q, x * (1 - x) ≤ V) :
    (p - q) ^ 2 / (2 * V) ≤
      p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q)) := by
  have hq0 : 0 < q := by linarith
  let G : ℝ → ℝ := fun x => -p * Real.log x - (1 - p) * Real.log (1 - x) - (x - p) ^ 2 / (2 * V)
  have hcont : ContinuousOn G (Set.Icc p q) := by
    have h1 : ContinuousOn (fun x : ℝ => -p * Real.log x) (Set.Icc p q) := by
      by_cases hp0 : p = 0
      · subst hp0; simp only [neg_zero, zero_mul]; exact continuousOn_const
      · have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
        exact continuousOn_const.mul (Real.continuousOn_log.mono (fun x hx => by
          have : 0 < x := lt_of_lt_of_le hp' hx.1
          exact this.ne'))
    have h2 : ContinuousOn (fun x : ℝ => (1 - p) * Real.log (1 - x)) (Set.Icc p q) :=
      continuousOn_const.mul ((Real.continuousOn_log).comp (continuousOn_const.sub continuousOn_id)
        (fun x hx => by
          have : x < 1 := lt_of_le_of_lt hx.2 hq
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith))
    have h3 : ContinuousOn (fun x : ℝ => (x - p) ^ 2 / (2 * V)) (Set.Icc p q) := by fun_prop
    exact (h1.sub h2).sub h3
  have hmono : MonotoneOn G (Set.Icc p q) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc p q) hcont
    · intro x hx
      rw [interior_Icc] at hx
      have hx0 : 0 < x := by linarith [hx.1]
      have hx1 : x < 1 := by linarith [hx.2]
      have : DifferentiableAt ℝ (fun x : ℝ => -p * Real.log x - (1 - p) * Real.log (1 - x) - (x - p) ^ 2 / (2 * V)) x := by
        have a1 : DifferentiableAt ℝ Real.log x := Real.differentiableAt_log hx0.ne'
        have a2 : DifferentiableAt ℝ (fun x : ℝ => Real.log (1 - x)) x :=
          (Real.differentiableAt_log (by linarith : (1 - x) ≠ 0)).comp x (by fun_prop)
        fun_prop
      exact this.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx0 : 0 < x := by linarith [hx.1]
      have hx1 : x < 1 := by linarith [hx.2]
      have hd : HasDerivAt G (-p * x⁻¹ - (1 - p) * ((-1) / (1 - x)) - 2 * (x - p) / (2 * V)) x := by
        have a1 : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0.ne'
        have a2 : HasDerivAt (fun x : ℝ => Real.log (1 - x)) ((-1) / (1 - x)) x := by
          have := ((hasDerivAt_id x).const_sub 1).log (by simp; linarith)
          simpa [div_eq_inv_mul] using this
        have a3 : HasDerivAt (fun x : ℝ => (x - p) ^ 2 / (2 * V)) (2 * (x - p) / (2 * V)) x := by
          have := ((hasDerivAt_id x).sub_const p).pow 2
          have := this.div_const (2 * V)
          simpa using this
        exact ((a1.const_mul (-p)).sub (a2.const_mul (1 - p))).sub a3
      rw [hd.deriv]
      have hxV : x * (1 - x) ≤ V := hVb x ⟨hx.1.le, hx.2.le⟩
      have hxp : 0 < x - p := by linarith [hx.1]
      have h1x : 0 < 1 - x := by linarith
      have : -p * x⁻¹ - (1 - p) * ((-1) / (1 - x)) - 2 * (x - p) / (2 * V)
          = (x - p) / (x * (1 - x)) - (x - p) / V := by
        field_simp
        ring
      rw [this, sub_nonneg]
      exact div_le_div_of_nonneg_left hxp.le (by positivity) hxV
  have hG := hmono ⟨le_refl p, hpq.le⟩ ⟨hpq.le, le_refl q⟩ hpq.le
  simp only [G] at hG
  have hlogp : p * Real.log (p / q) = p * Real.log p - p * Real.log q := by
    rcases hp.eq_or_lt with h | h
    · rw [← h]; simp
    · rw [Real.log_div h.ne' hq0.ne']; ring
  have h1p : 0 < 1 - p := by linarith
  have h1q : 0 < 1 - q := by linarith
  have hlog1 : (1 - p) * Real.log ((1 - p) / (1 - q)) = (1 - p) * Real.log (1 - p) - (1 - p) * Real.log (1 - q) := by
    rw [Real.log_div h1p.ne' h1q.ne']; ring
  rw [hlogp, hlog1]
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, sub_zero] at hG
  have : (p - q) ^ 2 = (q - p) ^ 2 := by ring
  rw [this]
  linarith

theorem solution (p q : ℝ) (hp : 0 ≤ p) (hpq : p < q) (hq : q ≤ 1) :
    ENNReal.ofReal ((p - q) ^ 2 /
      (2 * sSup ((fun x : ℝ => x * (1 - x)) '' Set.Icc p q))) ≤ ExploreFirst.FundIneq.klBer p q ∧
    (p - q) ^ 2 / (2 * q) ≤
      (p - q) ^ 2 / (2 * sSup ((fun x : ℝ => x * (1 - x)) '' Set.Icc p q)) := by
  have hbdd : BddAbove ((fun x : ℝ => x * (1 - x)) '' Set.Icc p q) := by
    refine ⟨1 / 4, ?_⟩
    rintro _ ⟨x, _, rfl⟩
    nlinarith [sq_nonneg (x - 1 / 2)]
  have hVb : ∀ x ∈ Set.Icc p q, x * (1 - x) ≤ sSup ((fun x : ℝ => x * (1 - x)) '' Set.Icc p q) :=
    fun x hx => le_csSup hbdd ⟨x, hx, rfl⟩
  set V := sSup ((fun x : ℝ => x * (1 - x)) '' Set.Icc p q) with hVdef
  have hVpos : 0 < V := by
    have hm : (p + q) / 2 ∈ Set.Icc p q := ⟨by linarith, by linarith⟩
    have := hVb _ hm
    have h2 : 0 < (p + q) / 2 * (1 - (p + q) / 2) := by
      apply mul_pos <;> linarith
    linarith
  have hVq : V ≤ q := by
    refine csSup_le ⟨p * (1 - p), p, ⟨le_refl p, hpq.le⟩, rfl⟩ ?_
    rintro _ ⟨x, hx, rfl⟩
    nlinarith [hx.1, hx.2]
  refine ⟨?_, ?_⟩
  · rcases hq.lt_or_eq with hq1 | hq1
    · rw [kl_bern p q hp (by linarith) (by linarith) hq1]
      exact ENNReal.ofReal_le_ofReal (kl_real p q V hp hpq hq1 hVpos hVb)
    · rw [hq1, kl_bern_one p (by linarith)]
      exact le_top
  · have hq0 : 0 < q := by linarith
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    linarith
