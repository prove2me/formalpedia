-- Prove2me | solution 1 for AvramDividend.Classical.strip_initial_excess_admissible_value
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T21:31:02.328791+00:00
-- url     : https://prove2.me/submissions/69be6e19-04d5-4db3-962d-c42db83c0e99

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option autoImplicit false

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

open AvramDividend.Classical in
theorem s2c817d06_dm_lump {Ω : Type*} (E : ℝ≥0 → Ω → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) (ω : Ω)
    (h0 : E 0 ω = 0) (hm : Monotone fun t => E t ω) :
    dividendMeasure (fun t ω => if t = 0 then 0 else δ + E t ω) ω
      = dividendMeasure E ω + ENNReal.ofReal δ • Measure.dirac 0 := by
  have hE : Monotone (fun t : ℝ => E t.toNNReal ω) := hm.comp (fun _ _ h => Real.toNNReal_mono h)
  have hF : Monotone (fun t : ℝ =>
      (fun (t : ℝ≥0) (ω : Ω) => if t = 0 then (0:ℝ) else δ + E t ω) t.toNNReal ω) := by
    intro a b hab
    simp only
    split_ifs with ha hb hb
    · exact le_rfl
    · have := hm (show (0:ℝ≥0) ≤ b.toNNReal from zero_le)
      simp only [h0] at this
      linarith
    · exfalso
      have := Real.toNNReal_mono hab
      rw [hb] at this
      exact ha (le_antisymm this zero_le)
    · have := hm (Real.toNNReal_mono hab)
      simp only at this
      linarith
  unfold dividendMeasure
  rw [dif_pos hF, dif_pos hE]
  have hS : ∀ y, hF.stieltjesFunction y = hE.stieltjesFunction y + if 0 ≤ y then δ else 0 := by
    intro y
    rw [Monotone.stieltjesFunction_eq, Monotone.stieltjesFunction_eq]
    split_ifs with hy
    · apply rightLim_eq_of_tendsto
      refine Tendsto.congr' ?_ ((hE.tendsto_rightLim y).add_const δ)
      filter_upwards [self_mem_nhdsWithin] with t ht
      have : t.toNNReal ≠ 0 := by
        rw [Ne, Real.toNNReal_eq_zero, not_le]
        exact lt_of_le_of_lt hy ht
      simp only [this, if_false]
      ring
    · rw [add_zero]
      apply rightLim_eq_of_tendsto
      refine Tendsto.congr' ?_ (hE.tendsto_rightLim y)
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds (not_le.mp hy))]
        with t ht
      have : t.toNNReal = 0 := Real.toNNReal_eq_zero.mpr (le_of_lt ht)
      simp only [this, if_true, h0]
  refine Measure.ext_of_Ioc _ _ (fun a b hab => ?_)
  rw [Measure.add_apply, Measure.smul_apply, StieltjesFunction.measure_Ioc,
    StieltjesFunction.measure_Ioc, hS, hS, Measure.dirac_apply, smul_eq_mul]
  have hmono := hE.stieltjesFunction.mono hab.le
  by_cases ha : 0 ≤ a
  · have hb : 0 ≤ b := ha.trans hab.le
    have hn : (0:ℝ) ∉ Ioc a b := fun h => absurd h.1 (not_lt.mpr ha)
    rw [if_pos ha, if_pos hb, Set.indicator_of_notMem hn, mul_zero, add_zero]
    congr 1
    ring
  · by_cases hb : 0 ≤ b
    · have hmem : (0:ℝ) ∈ Ioc a b := ⟨not_le.mp ha, hb⟩
      rw [if_neg ha, if_pos hb, Set.indicator_of_mem hmem, Pi.one_apply, mul_one,
        ← ENNReal.ofReal_add (sub_nonneg.mpr hmono) hδ]
      congr 1
      ring
    · have hn : (0:ℝ) ∉ Ioc a b := fun h => hb h.2
      rw [if_neg ha, if_neg hb, Set.indicator_of_notMem hn, mul_zero, add_zero, add_zero,
        add_zero]

open AvramDividend.Classical in
theorem s2c817d06_ruin {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x c : ℝ) (hc : 0 ≤ c) (hcx : c < x)
    (E : ℝ≥0 → Ω → ℝ) (ω : Ω) (h0 : E 0 ω = 0) :
    ruinTime X x (fun t ω => if t = 0 then 0 else (x - c) + E t ω) ω = ruinTime X c E ω := by
  have hr : ∀ t, (riskProcess X x (fun t ω => if t = 0 then 0 else (x - c) + E t ω) t ω < 0 ↔
      riskProcess X c E t ω < 0) := by
    intro t
    unfold riskProcess
    by_cases ht : t = 0
    · subst ht
      simp only [if_true, X.X_zero, h0]
      constructor <;> intro h <;> linarith
    · simp only [ht, if_false]
      constructor <;> intro h <;> linarith
  unfold ruinTime
  simp only [hr]

open AvramDividend.Classical in
theorem s2c817d06_value {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x c : ℝ)
    (hc : 0 ≤ c) (hcx : c < x)
    (E : ℝ≥0 → Ω → ℝ)
    (h0 : ∀ ω, E 0 ω = 0) (hmono : ∀ ω, Monotone fun t => E t ω) :
    dividendValue X q x
        (fun t ω => if t = 0 then 0 else (x - c) + E t ω) =
      ENNReal.ofReal (x - c) + dividendValue X q c E := by
  classical
  have := X.isProbability
  have hδ : 0 ≤ x - c := by linarith
  have hpt : ∀ ω, (∫⁻ t in paymentTimes (ruinTime X x
        (fun t ω => if t = 0 then 0 else (x - c) + E t ω) ω),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure (fun t ω => if t = 0 then 0 else (x - c) + E t ω) ω)) =
      (∫⁻ t in paymentTimes (ruinTime X c E ω),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure E ω)) + ENNReal.ofReal (x - c) := by
    intro ω
    have hmem : (0:ℝ) ∈ paymentTimes (ruinTime X c E ω) := ⟨le_rfl, Or.inl rfl⟩
    rw [s2c817d06_ruin X x c hc hcx E ω (h0 ω), s2c817d06_dm_lump E (x - c) hδ ω (h0 ω) (hmono ω),
      Measure.restrict_add, lintegral_add_measure, Measure.restrict_smul, lintegral_smul_measure,
      restrict_dirac, if_pos hmem, lintegral_dirac]
    simp
  unfold dividendValue
  simp_rw [hpt]
  rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one, add_comm]

open AvramDividend.Classical in
theorem s2c817d06_lb {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x c : ℝ) (hc : 0 ≤ c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D) (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    x - c ≤ D t ω := by
  have hmono := hD.1.1.2.1 ω
  have hcap : ∀ s : ℝ≥0, 0 < s → x + X.X s ω - D s ω ≤ c := by
    intro s hs
    have := hD.2 ω s hs
    unfold riskProcess at this
    exact (ENNReal.ofReal_le_ofReal_iff hc).mp this
  have hX : Tendsto (fun s => X.X s ω) (𝓝[>] (0:ℝ≥0)) (𝓝 0) := by
    have h := (X.rightCont ω 0).tendsto.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    simpa only [X.X_zero] using h
  have hlim : Tendsto (fun s => x - c + X.X s ω) (𝓝[>] (0:ℝ≥0)) (𝓝 (x - c + 0)) :=
    hX.const_add _
  rw [add_zero] at hlim
  apply le_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsGT ht] with s hs
  have h1 := hcap s hs.1
  have h2 := hmono hs.2.le
  simp only at h2
  linarith

open MeasureTheory Filter Set Topology NNReal ENNReal AvramDividend.Classical in
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x c : ℝ)
    (hc : 0 ≤ c) (hcx : c < x)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D) :
    IsAdmissibleLe X c (ENNReal.ofReal c)
        (fun t ω => if t = 0 then 0 else D t ω - (x - c)) ∧
      dividendValue X q x D =
        ENNReal.ofReal (x - c) +
          dividendValue X q c
            (fun t ω => if t = 0 then 0 else D t ω - (x - c)) := by
  classical
  have hlb := s2c817d06_lb X x c hc D hD
  obtain ⟨⟨⟨h0, hmono, hlc, had⟩, hadm⟩, hcap⟩ := hD
  set E : ℝ≥0 → Ω → ℝ := fun t ω => if t = 0 then 0 else D t ω - (x - c) with hEdef
  have hE0 : ∀ ω, E 0 ω = 0 := fun ω => by simp [hEdef]
  have hEmono : ∀ ω, Monotone fun t => E t ω := by
    intro ω a b hab
    simp only [hEdef]
    by_cases ha : a = 0
    · rw [if_pos ha]
      by_cases hb : b = 0
      · rw [if_pos hb]
      · rw [if_neg hb]
        have := hlb ω b (pos_iff_ne_zero.mpr hb)
        linarith
    · have hb : b ≠ 0 := fun hb => ha (le_antisymm (hb ▸ hab) zero_le)
      rw [if_neg ha, if_neg hb]
      have := hmono ω hab
      simp only at this
      linarith
  have hDE : D = fun t ω => if t = 0 then 0 else (x - c) + E t ω := by
    funext t ω
    by_cases ht : t = 0
    · subst ht; simp [h0]
    · simp [hEdef, ht]
  have hrisk : ∀ ω t, t ≠ 0 → riskProcess X c E t ω = riskProcess X x D t ω := by
    intro ω t ht
    simp only [riskProcess, hEdef, if_neg ht]
    ring
  have hruin : ∀ ω, ruinTime X c E ω = ruinTime X x D ω := by
    intro ω
    have hr : ∀ t, (riskProcess X c E t ω < 0 ↔ riskProcess X x D t ω < 0) := by
      intro t
      by_cases ht : t = 0
      · subst ht
        simp only [riskProcess, X.X_zero, hE0, h0]
        constructor <;> intro h <;> linarith
      · rw [hrisk ω t ht]
    unfold ruinTime
    simp only [hr]
  have hrl : ∀ ω t, rightLimit E t ω ≤ rightLimit D t ω - (x - c) := by
    intro ω t
    unfold rightLimit
    have hne : Nonempty (Ioi t) := ⟨⟨t + 1, by simp⟩⟩
    have hbdd : BddBelow (Set.range fun s : Ioi t => E s ω) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨s, rfl⟩
      have := hEmono ω (zero_le : (0:ℝ≥0) ≤ s)
      simp only [hE0] at this
      exact this
    have : (⨅ s : Ioi t, E s ω) + (x - c) ≤ ⨅ s : Ioi t, D s ω := by
      apply le_ciInf
      intro s
      have hs : (s : ℝ≥0) ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le s.2)
      have := ciInf_le hbdd s
      simp only [hEdef, if_neg hs] at this
      linarith
    linarith
  refine ⟨⟨⟨⟨hE0, hEmono, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro ω t
    by_cases ht : t = 0
    · subst ht
      have : Iic (0:ℝ≥0) = {0} := by
        ext s
        simp only [mem_Iic, mem_singleton_iff]
        exact nonpos_iff_eq_zero
      rw [this]
      exact continuousWithinAt_singleton
    · have hc' : ContinuousWithinAt (fun s => D s ω - (x - c)) (Iic t) t :=
        (hlc ω t).sub continuousWithinAt_const
      apply hc'.congr_of_eventuallyEq
      · filter_upwards [eventually_nhdsWithin_of_eventually_nhds
          (Ioi_mem_nhds (pos_iff_ne_zero.mpr ht))] with s hs
        simp only [hEdef, if_neg (ne_of_gt (show (0:ℝ≥0) < s from hs))]
      · simp only [hEdef, if_neg ht]
  · intro t
    by_cases ht : t = 0
    · have : E t = fun _ => 0 := by funext ω; simp [hEdef, ht]
      rw [this]
      exact measurable_const
    · have : E t = fun ω => D t ω - (x - c) := by funext ω; simp [hEdef, ht]
      rw [this]
      exact (had t).sub measurable_const
  · intro ω t ht
    by_cases ht0 : t = 0
    · subst ht0
      have h := hadm ω 0 (Or.inl rfl)
      have := hrl ω 0
      simp only [riskProcess, X.X_zero, hE0, h0] at h ⊢
      linarith
    · have ht' : (t : ℝ≥0∞) < ruinTime X x D ω := by
        rcases ht with h | h
        · exact absurd h ht0
        · rwa [hruin ω] at h
      have h := hadm ω t (Or.inr ht')
      have := hrl ω t
      rw [hrisk ω t ht0]
      have hEt : E t ω = D t ω - (x - c) := by simp [hEdef, ht0]
      rw [hEt]
      linarith
  · intro ω t ht
    rw [hrisk ω t (ne_of_gt ht)]
    exact hcap ω t ht
  · rw [hDE]
    exact s2c817d06_value X q x c hc hcx E hE0 hEmono
