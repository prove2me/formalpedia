-- Prove2me | solution 1 for ChenFarias.SimplePolicy.expected_max
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T18:46:40.015232+00:00
-- url     : https://prove2.me/submissions/9032395d-2211-4f6b-a2df-3d439f45126f

import Mathlib

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

lemma cf_lintegral_expMeasure (β : ℝ) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ s, g s ∂expMeasure β =
      ∫⁻ s in Ici 0, ENNReal.ofReal (β * Real.exp (-(β * s))) * g s := by
  have hpdf : Measurable (exponentialPDF β) :=
    (measurable_exponentialPDFReal β).ennreal_ofReal
  have : expMeasure β = volume.withDensity (exponentialPDF β) := rfl
  rw [this, lintegral_withDensity_eq_lintegral_mul _ hpdf hg]
  have hind : (exponentialPDF β * g) =
      (Ici (0:ℝ)).indicator (fun s => ENNReal.ofReal (β * Real.exp (-(β * s))) * g s) := by
    funext s
    by_cases hs : 0 ≤ s
    · simp [Set.indicator_of_mem (show s ∈ Ici (0:ℝ) from hs), exponentialPDF_of_nonneg hs]
    · push Not at hs
      simp [Set.indicator_of_notMem (show s ∉ Ici (0:ℝ) from not_le.2 hs),
        exponentialPDF_of_neg hs]
  rw [hind, lintegral_indicator measurableSet_Ici]

lemma cf_lintegral_Ioi_FTC {g g' : ℝ → ℝ} {a l : ℝ}
    (hderiv : ∀ x ∈ Ici a, HasDerivAt g (g' x) x) (hpos : ∀ x ∈ Ioi a, 0 ≤ g' x)
    (hg : Tendsto g atTop (𝓝 l)) :
    ∫⁻ x in Ioi a, ENNReal.ofReal (g' x) = ENNReal.ofReal (l - g a) := by
  have hint := integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hg
  rw [← integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hg,
    ofReal_integral_eq_lintegral_ofReal hint]
  exact (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hpos)

theorem solution (β T : ℝ) (hβ : 0 < β) (hT : 0 < T) :
    (∫⁻ s, ENNReal.ofReal (max 1 (s / T)) ∂expMeasure β) =
      ENNReal.ofReal (1 + Real.exp (-(β * T)) / (β * T)) := by
  have := isProbabilityMeasure_expMeasure hβ
  have hsplit : ∀ s, ENNReal.ofReal (max 1 (s / T)) =
      1 + ENNReal.ofReal (max 0 ((s - T) / T)) := by
    intro s
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (le_max_left _ _)]
    congr 1
    rcases le_total s T with h | h
    · have h1 : (s - T) / T ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hT.le
      have h2 : s / T ≤ 1 := (div_le_one hT).2 h
      rw [max_eq_left h2, max_eq_left h1]; ring
    · have h1 : 0 ≤ (s - T) / T := div_nonneg (by linarith) hT.le
      have h2 : 1 ≤ s / T := (one_le_div hT).2 h
      rw [max_eq_right h2, max_eq_right h1]; field_simp; ring
  simp_rw [hsplit]
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, one_mul]
  have hmeas : Measurable (fun s : ℝ => ENNReal.ofReal (max 0 ((s - T) / T))) := by
    fun_prop
  rw [cf_lintegral_expMeasure β hmeas]
  -- restrict to Ioi T
  have hzero : ∀ s ∈ Ici (0:ℝ), s ∉ Ioi T →
      ENNReal.ofReal (β * Real.exp (-(β * s))) * ENNReal.ofReal (max 0 ((s - T) / T)) = 0 := by
    intro s _ hs
    have : (s - T) / T ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by simp at hs; linarith) hT.le
    simp [max_eq_left this]
  have hsub : Ioi T ⊆ Ici (0:ℝ) := fun s hs => le_of_lt (lt_trans hT hs)
  have hrestr : ∫⁻ s in Ici 0, ENNReal.ofReal (β * Real.exp (-(β * s))) *
        ENNReal.ofReal (max 0 ((s - T) / T)) =
      ∫⁻ s in Ioi T, ENNReal.ofReal (β * (s - T) / T * Real.exp (-(β * s))) := by
    rw [← lintegral_indicator measurableSet_Ici, ← lintegral_indicator measurableSet_Ioi]
    congr 1
    funext s
    by_cases h1 : s ∈ Ioi T
    · rw [Set.indicator_of_mem h1, Set.indicator_of_mem (hsub h1)]
      have : 0 ≤ (s - T) / T := div_nonneg (by simp at h1; linarith) hT.le
      rw [max_eq_right this, ← ENNReal.ofReal_mul (by positivity)]
      congr 1; ring
    · rw [Set.indicator_of_notMem h1]
      by_cases h2 : s ∈ Ici (0:ℝ)
      · rw [Set.indicator_of_mem h2, hzero s h2 h1]
      · rw [Set.indicator_of_notMem h2]
  rw [hrestr]
  -- antiderivative
  set g : ℝ → ℝ := fun s => -(((s - T) / T + 1 / (β * T)) * Real.exp (-(β * s))) with hgdef
  have hderiv : ∀ x ∈ Ici T, HasDerivAt g (β * (x - T) / T * Real.exp (-(β * x))) x := by
    intro x _
    have h1 : HasDerivAt (fun s : ℝ => (s - T) / T + 1 / (β * T)) (1 / T) x := by
      have := ((hasDerivAt_id x).sub_const T).div_const T
      simpa using this.add_const (1 / (β * T))
    have h2 : HasDerivAt (fun s : ℝ => Real.exp (-(β * s))) (Real.exp (-(β * x)) * (-β)) x := by
      have := ((hasDerivAt_id x).const_mul β).neg.exp
      simpa using this
    have h3 : HasDerivAt (fun s => -(((s - T) / T + 1 / (β * T)) * Real.exp (-(β * s))))
        (-(1 / T * Real.exp (-(β * x)) + ((x - T) / T + 1 / (β * T)) *
          (Real.exp (-(β * x)) * -β))) x := (h1.mul h2).neg
    refine h3.congr_deriv ?_
    have hb : β ≠ 0 := hβ.ne'
    have ht : T ≠ 0 := hT.ne'
    field_simp
    ring
  have hpos : ∀ x ∈ Ioi T, 0 ≤ β * (x - T) / T * Real.exp (-(β * x)) := by
    intro x hx
    have : 0 ≤ x - T := by simp at hx; linarith
    positivity
  have htend : Tendsto g atTop (𝓝 0) := by
    have hA : Tendsto (fun s : ℝ => s * Real.exp (-β * s)) atTop (𝓝 0) := by
      simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 β hβ
    have hB : Tendsto (fun s : ℝ => Real.exp (-β * s)) atTop (𝓝 0) := by
      have := Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop hβ)
      simpa [Function.comp_def, neg_mul] using this
    have := ((hA.div_const T).add ((hB.const_mul (-1 + 1 / (β * T))))).neg
    simp only [zero_div, mul_zero, add_zero, neg_zero] at this
    refine this.congr (fun s => ?_)
    simp only [hgdef, neg_mul]
    field_simp
    ring
  have hgT : 0 - g T = Real.exp (-(β * T)) / (β * T) := by
    simp only [hgdef, sub_self, zero_div, zero_add]
    ring
  rw [cf_lintegral_Ioi_FTC hderiv hpos htend, hgT]
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by positivity)]
