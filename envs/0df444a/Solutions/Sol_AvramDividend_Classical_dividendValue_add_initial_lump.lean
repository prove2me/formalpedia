-- Prove2me | solution 1 for AvramDividend.Classical.dividendValue_add_initial_lump
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T20:29:57.245259+00:00
-- url     : https://prove2.me/submissions/3211f494-5f89-4517-8919-b91b526d8947

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option autoImplicit false

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

open AvramDividend.Classical in
theorem a0df7aaf_dm_lump {Ω : Type*} (E : ℝ≥0 → Ω → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) (ω : Ω)
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
theorem a0df7aaf_ruin {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
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

open MeasureTheory Filter Set Topology NNReal ENNReal AvramDividend.Classical in
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x c : ℝ)
    (hc : 0 ≤ c) (hcx : c < x)
    (E : ℝ≥0 → Ω → ℝ)
    (hE : IsAdmissibleLe X c (ENNReal.ofReal c) E) :
    dividendValue X q x
        (fun t ω => if t = 0 then 0 else (x - c) + E t ω) =
      ENNReal.ofReal (x - c) + dividendValue X q c E := by
  classical
  have := X.isProbability
  obtain ⟨⟨⟨h0, hmono, -, -⟩, -⟩, -⟩ := hE
  have hδ : 0 ≤ x - c := by linarith
  have hpt : ∀ ω, (∫⁻ t in paymentTimes (ruinTime X x
        (fun t ω => if t = 0 then 0 else (x - c) + E t ω) ω),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure (fun t ω => if t = 0 then 0 else (x - c) + E t ω) ω)) =
      (∫⁻ t in paymentTimes (ruinTime X c E ω),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure E ω)) + ENNReal.ofReal (x - c) := by
    intro ω
    have hmem : (0:ℝ) ∈ paymentTimes (ruinTime X c E ω) := ⟨le_rfl, Or.inl rfl⟩
    rw [a0df7aaf_ruin X x c hc hcx E ω (h0 ω), a0df7aaf_dm_lump E (x - c) hδ ω (h0 ω) (hmono ω),
      Measure.restrict_add, lintegral_add_measure, Measure.restrict_smul, lintegral_smul_measure,
      restrict_dirac, if_pos hmem, lintegral_dirac]
    simp
  unfold dividendValue
  simp_rw [hpt]
  rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one, add_comm]
