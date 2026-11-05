-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_original_mark_mean_compact_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:36:52.62564+00:00
-- url     : https://prove2.me/submissions/e484869f-bcbc-4fce-aff1-37f4bcee5178

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_nonnegative_compact_jump_lintegral
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_finite_compact_test_mark_lintegral
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_compact_negative_test_vanishes_near_zero
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_public_mark_kernel_tonelli
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Original mark marginal from the proved pathwise kernel Tonelli theorem,
    with the original finite jump-sum mean and no intermediate private imports. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T)
    (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g))
    (hneg : tsupport g ⊆ Set.Iio (0 : ℝ))
    (hgnonneg : ∀ y : ℝ, 0 ≤ g y) :
    ∃ markRate : Measure ℝ,
      (∀ B : Set ℝ, MeasurableSet B →
        markRate B = (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ B) ∂P)) ∧
      (∫⁻ y, ENNReal.ofReal (g y) ∂markRate) =
        ENNReal.ofReal ((T : ℝ) *
          (∫ y : ℝ, g y ∂(X.ν.restrict (Iio (0 : ℝ))))) := by
  classical
  have hgm : Measurable (fun y : ℝ => ENNReal.ofReal (g y)) :=
    ENNReal.measurable_ofReal.comp hg.measurable
  let A : Set (ℝ≥0 × ℝ) := Ioc (0 : ℝ≥0) T ×ˢ (Set.univ : Set ℝ)
  have hA : MeasurableSet A := measurableSet_Ioc.prod MeasurableSet.univ
  let φ : (ℝ≥0 × ℝ) → ℝ≥0∞ :=
    A.indicator (fun p => ENNReal.ofReal (g p.2))
  have hφ : Measurable φ := (hgm.comp measurable_snd).indicator hA
  obtain ⟨M, hM, hTonelli⟩ :=
    avram_p2_a_zero_rate_original_public_mark_kernel_tonelli X φ hφ
  let sndMap : ℝ≥0 × ℝ → ℝ := Prod.snd
  let markRate : Measure ℝ := (M.restrict A).map sndMap
  have hmark (B : Set ℝ) (hB : MeasurableSet B) :
      markRate B =
        (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ B) ∂P) := by
    have hsndB : MeasurableSet (Set.preimage sndMap B) :=
      hB.preimage measurable_snd
    have hset : (Set.preimage sndMap B) ∩ A = Ioc 0 T ×ˢ B := by
      ext p
      simp only [A, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_prod, Set.mem_univ, and_true, sndMap]
      exact and_comm
    change ((M.restrict A).map sndMap) B = _
    rw [Measure.map_apply measurable_snd hB]
    rw [Measure.restrict_apply hsndB, hset]
    exact hM _ (measurableSet_Ioc.prod hB)
  obtain ⟨J, hJ, hJfin, hJnonneg, hJmean⟩ :=
    avram_p2_a_zero_rate_original_nonnegative_compact_jump_lintegral
      P X T hT g hg hc hneg hgnonneg
  obtain ⟨ε, hε, hvanAbs⟩ :=
    avram_p2_a_zero_rate_compact_negative_test_vanishes_near_zero
      g hg hc hneg
  have hvan (y : ℝ) (h : dist y 0 < ε) : g y = 0 :=
    hvanAbs y (by simpa [Real.dist_eq] using h)
  let N : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  have hpath (ω : Ω) :
      (∫⁻ p : ℝ≥0 × ℝ,
        (if p.1 ∈ Ioc (0 : ℝ≥0) T then ENNReal.ofReal (g p.2) else 0) ∂N ω) =
        ENNReal.ofReal (J ω) := by
    obtain ⟨F, hF, hcount⟩ :=
      avram_p2_a_zero_rate_original_finite_compact_test_mark_lintegral
        X ω T g hg ε hε hvan
    obtain ⟨G, hG, hJG⟩ := hJfin ω
    have hFG : F = G := Finset.ext (fun u => (hF u).trans (hG u).symm)
    rw [← hFG] at hJG
    have hsum :
        (∑ u ∈ F, ENNReal.ofReal (g (X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) =
          ENNReal.ofReal (J ω) := by
      rw [hJG]
      exact (ENNReal.ofReal_sum_of_nonneg
        (by intro u hu; exact hgnonneg _)).symm
    exact hcount.trans hsum
  refine ⟨markRate, hmark, ?_⟩
  calc
    (∫⁻ y, ENNReal.ofReal (g y) ∂markRate) =
      (∫⁻ p, φ p ∂M) := by
        change (∫⁻ y, ENNReal.ofReal (g y) ∂((M.restrict A).map sndMap)) = _
        rw [lintegral_map hgm measurable_snd]
        exact (lintegral_indicator hA
          (fun p : ℝ≥0 × ℝ => ENNReal.ofReal (g p.2))).symm
    _ = (∫⁻ ω, ∫⁻ p : ℝ≥0 × ℝ, φ p ∂N ω ∂P) := hTonelli
    _ = (∫⁻ ω, ∫⁻ p : ℝ≥0 × ℝ,
      (if p.1 ∈ Ioc (0 : ℝ≥0) T then ENNReal.ofReal (g p.2) else 0)
        ∂N ω ∂P) := by
          simp [φ, A, Set.indicator, Set.mem_prod]
    _ = (∫⁻ ω, ENNReal.ofReal (J ω) ∂P) :=
      lintegral_congr_ae (Filter.Eventually.of_forall hpath)
    _ = _ := hJmean
