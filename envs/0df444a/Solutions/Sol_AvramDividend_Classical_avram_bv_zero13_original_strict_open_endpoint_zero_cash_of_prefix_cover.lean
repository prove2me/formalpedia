-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_zero13_original_strict_open_endpoint_zero_cash_of_prefix_cover
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T00:48:54.090558+00:00
-- url     : https://prove2.me/submissions/08cc9acc-f0c0-4618-be42-0e3868d0dcc2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_all_pathwise_restart_zero_weighted_cash_no_survival
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- Strict open-endpoint dividend cash from simultaneous actual-process prefix cash. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (hDrift : 0 ≤ X.drift)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ≥0) (hH : 0 < H) :
    ∀ᵐ ω ∂P,
      ∀ (s J : ℝ≥0), s < J → J ≤ H →
      ∀ (a : ℕ → ℝ≥0),
      (∀ n, s ≤ a n ∧ a n < J) →
      Monotone (fun n : ℕ => Ioc (s : ℝ) ((a n : ℝ≥0) : ℝ)) →
      (⋃ n, Ioc (s : ℝ) ((a n : ℝ≥0) : ℝ)) =
        Ioo (s : ℝ) (J : ℝ) →
      (∀ u : ℝ≥0, s ≤ u → u < J →
        riskProcess X x D u ω -
          (rightLimit D u ω - D u ω) = 0) →
      (∀ u : ℝ≥0, u ∈ Ioo s J →
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) →
      ∀ f : ℝ → ℝ≥0∞, Measurable f →
        (∫⁻ t in Ioo (s : ℝ) (J : ℝ), f t
          ∂(dividendMeasure D ω)) =
        (∫⁻ t in Ioo (s : ℝ) (J : ℝ), f t
          ∂((ENNReal.ofReal X.drift) • volume)) := by
  filter_upwards [
    avram_bv_zero13_original_all_pathwise_restart_zero_weighted_cash_no_survival
      X hBV hFinite hDrift x C D hD H hH] with ω hbase
  intro s J hsj hJH a hRange hMono hCover hzero hnoj f hf
  have hprefix (n : ℕ) :
      (∫⁻ t in Ioc (s : ℝ) ((a n : ℝ≥0) : ℝ), f t
        ∂(dividendMeasure D ω)) =
      (∫⁻ t in Ioc (s : ℝ) ((a n : ℝ≥0) : ℝ), f t
        ∂((ENNReal.ofReal X.drift) • volume)) := by
    obtain ⟨hsAn, haJ⟩ := hRange n
    exact hbase s (a n) hsAn (le_trans (le_of_lt haJ) hJH)
      (by
        intro u hsu huAn
        exact hzero u hsu (lt_of_le_of_lt huAn haJ))
      (by
        intro u hu
        exact hnoj u ⟨hu.1, lt_of_le_of_lt hu.2 haJ⟩) f
  have hMonoF : Monotone
      (fun n : ℕ => (Ioc (s : ℝ) ((a n : ℝ≥0) : ℝ)).indicator f) := by
    intro n m hnm t
    by_cases ht : t ∈ Ioc (s : ℝ) ((a n : ℝ≥0) : ℝ)
    · have ht' := hMono hnm ht
      simp [Set.indicator_of_mem ht, Set.indicator_of_mem ht']
    · simp [Set.indicator_of_notMem ht]
  have hPoint (t : ℝ) :
      (Ioo (s : ℝ) (J : ℝ)).indicator f t =
        ⨆ n, (Ioc (s : ℝ) ((a n : ℝ≥0) : ℝ)).indicator f t := by
    by_cases ht : t ∈ Ioo (s : ℝ) (J : ℝ)
    · have htU : t ∈ ⋃ n, Ioc (s : ℝ) ((a n : ℝ≥0) : ℝ) := by
        rw [hCover]
        exact ht
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp htU
      have hlow : f t ≤
          ⨆ n, (Ioc (s : ℝ) ((a n : ℝ≥0) : ℝ)).indicator f t := by
        exact le_iSup_of_le n (le_of_eq (Set.indicator_of_mem hn f).symm)
      have hupp :
          (⨆ n, (Ioc (s : ℝ) ((a n : ℝ≥0) : ℝ)).indicator f t) ≤ f t := by
        apply iSup_le
        intro k
        by_cases hk : t ∈ Ioc (s : ℝ) ((a k : ℝ≥0) : ℝ)
        · simp [Set.indicator_of_mem hk]
        · simp [Set.indicator_of_notMem hk]
      simpa [Set.indicator_of_mem ht] using (le_antisymm hupp hlow).symm
    · have hnot (n : ℕ) :
          t ∉ Ioc (s : ℝ) ((a n : ℝ≥0) : ℝ) := by
        intro hn
        apply ht
        rw [← hCover]
        exact Set.mem_iUnion.mpr ⟨n, hn⟩
      simp [Set.indicator_of_notMem ht, hnot]
  have hLimit (μ : Measure ℝ) :
      (∫⁻ t in Ioo (s : ℝ) (J : ℝ), f t ∂μ) =
        ⨆ n, (∫⁻ t in Ioc (s : ℝ) ((a n : ℝ≥0) : ℝ), f t ∂μ) := by
    calc
      _ = ∫⁻ t, (Ioo (s : ℝ) (J : ℝ)).indicator f t ∂μ :=
        (lintegral_indicator measurableSet_Ioo f).symm
      _ = ∫⁻ t, ⨆ n, (Ioc (s : ℝ) ((a n : ℝ≥0) : ℝ)).indicator f t ∂μ := by
        congr 1
        funext t
        exact hPoint t
      _ = ⨆ n, ∫⁻ t, (Ioc (s : ℝ) ((a n : ℝ≥0) : ℝ)).indicator f t ∂μ :=
        lintegral_iSup (fun n => hf.indicator measurableSet_Ioc) hMonoF
      _ = ⨆ n, (∫⁻ t in Ioc (s : ℝ) ((a n : ℝ≥0) : ℝ), f t ∂μ) := by
        simp_rw [lintegral_indicator measurableSet_Ioc f]
  calc
    _ = ⨆ n, (∫⁻ t in Ioc (s : ℝ) ((a n : ℝ≥0) : ℝ), f t
        ∂(dividendMeasure D ω)) := hLimit _
    _ = ⨆ n, (∫⁻ t in Ioc (s : ℝ) ((a n : ℝ≥0) : ℝ), f t
        ∂((ENNReal.ofReal X.drift) • volume)) := by
      congr 1
      funext n
      exact hprefix n
    _ = _ := (hLimit _).symm
