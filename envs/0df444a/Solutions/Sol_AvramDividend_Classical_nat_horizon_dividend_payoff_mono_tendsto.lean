-- Prove2me | solution 1 for AvramDividend.Classical.nat_horizon_dividend_payoff_mono_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T13:25:08.579179+00:00
-- url     : https://prove2.me/submissions/fd455492-dc69-48c4-a557-fddfeef7e358

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_eq_iUnion_nat_horizons


set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) :
    (∀ ω, Monotone (fun n : ℕ =>
      ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) ∧
    (∀ ω, Tendsto
      (fun n : ℕ =>
        ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      atTop
      (𝓝 (∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)))) := by
  have paymentTimes_mono :
      ∀ {a b : ℝ≥0∞}, a ≤ b → paymentTimes a ⊆ paymentTimes b := by
    intro a b hab t ht
    change 0 ≤ t ∧ (t = 0 ∨ ENNReal.ofReal t < a) at ht
    change 0 ≤ t ∧ (t = 0 ∨ ENNReal.ofReal t < b)
    exact ⟨ht.1, ht.2.imp_right (fun h => lt_of_lt_of_le h hab)⟩
  constructor
  · intro ω n m hnm
    apply lintegral_mono_set
    apply paymentTimes_mono
    apply min_le_min_left
    exact_mod_cast hnm
  · intro ω
    let σ : ℝ≥0∞ := ruinTime X x D ω
    let μ : Measure ℝ := dividendMeasure D ω
    let g : ℝ → ℝ≥0∞ :=
      fun t => ENNReal.ofReal (Real.exp (-(q * t)))
    let S : ℕ → Set ℝ :=
      fun n => paymentTimes (min σ (n : ℝ≥0∞))
    let T : Set ℝ := paymentTimes σ
    have hSmono : Monotone S := by
      intro n m hnm
      dsimp [S]
      apply paymentTimes_mono
      apply min_le_min_left
      exact_mod_cast hnm
    have hSsub : ∀ n, S n ⊆ T := by
      intro n
      dsimp [S, T]
      exact paymentTimes_mono (min_le_left _ _)
    have hFmono : Monotone (fun n : ℕ => ∫⁻ t in S n, g t ∂μ) := by
      intro n m hnm
      exact lintegral_mono_set (hSmono hnm)
    have hTmeas : MeasurableSet T := by
      dsimp [T]
      unfold paymentTimes
      measurability
    have hSmeas : ∀ n, MeasurableSet (S n) := by
      intro n
      dsimp [S]
      unfold paymentTimes
      measurability
    have hg : Measurable g := by
      dsimp [g]
      measurability
    have hIndMono : Monotone (fun n : ℕ => (S n).indicator g) := by
      intro n m hnm t
      change (S n).indicator g t ≤ (S m).indicator g t
      by_cases hn : t ∈ S n
      · have hm : t ∈ S m := hSmono hnm hn
        calc
          (S n).indicator g t = g t := Set.indicator_of_mem hn _
          _ ≤ g t := le_rfl
          _ = (S m).indicator g t := (Set.indicator_of_mem hm _).symm
      · calc
          (S n).indicator g t = 0 := Set.indicator_of_notMem hn _
          _ ≤ (S m).indicator g t := bot_le
    have hIndMeas :
        ∀ n, AEMeasurable ((S n).indicator g) μ := by
      intro n
      exact (hg.indicator (hSmeas n)).aemeasurable
    have hUnion : (⋃ n, S n) = T := by
      dsimp [S, T]
      simpa using (paymentTimes_eq_iUnion_nat_horizons σ).symm
    have hIndSup : ∀ t : ℝ,
        (⨆ n : ℕ, (S n).indicator g t) = T.indicator g t := by
      intro t
      apply le_antisymm
      · refine iSup_le ?_
        intro n
        by_cases hn : t ∈ S n
        · have ht : t ∈ T := hSsub n hn
          calc
            (S n).indicator g t = g t := Set.indicator_of_mem hn _
            _ ≤ g t := le_rfl
            _ = T.indicator g t := (Set.indicator_of_mem ht _).symm
        · calc
            (S n).indicator g t = 0 := Set.indicator_of_notMem hn _
            _ ≤ T.indicator g t := bot_le
      · by_cases ht : t ∈ T
        · have hu : t ∈ ⋃ n, S n := by
            rw [hUnion]
            exact ht
          rcases Set.mem_iUnion.mp hu with ⟨n, hn⟩
          have hle :
              (S n).indicator g t ≤
                ⨆ m : ℕ, (S m).indicator g t :=
            le_iSup (fun m : ℕ => (S m).indicator g t) n
          calc
            T.indicator g t = g t := Set.indicator_of_mem ht _
            _ = (S n).indicator g t := (Set.indicator_of_mem hn _).symm
            _ ≤ ⨆ m : ℕ, (S m).indicator g t := hle
        · calc
            T.indicator g t = 0 := Set.indicator_of_notMem ht _
            _ ≤ ⨆ m : ℕ, (S m).indicator g t := bot_le
    have hSup :
        (⨆ n, ∫⁻ t in S n, g t ∂μ) = ∫⁻ t in T, g t ∂μ := by
      calc
        (⨆ n, ∫⁻ t in S n, g t ∂μ) =
            ⨆ n, ∫⁻ t, (S n).indicator g t ∂μ := by
              apply iSup_congr
              intro n
              exact (lintegral_indicator (hSmeas n) g).symm
        _ = ∫⁻ t, ⨆ n, (S n).indicator g t ∂μ := by
              symm
              exact lintegral_iSup_directed hIndMeas hIndMono.directed_le
        _ = ∫⁻ t, T.indicator g t ∂μ := by
              apply lintegral_congr
              intro t
              exact hIndSup t
        _ = ∫⁻ t in T, g t ∂μ :=
              lintegral_indicator hTmeas g
    have hlim :
        Tendsto (fun n : ℕ => ∫⁻ t in S n, g t ∂μ)
          atTop (𝓝 (∫⁻ t in T, g t ∂μ)) := by
      simpa only [hSup] using (tendsto_atTop_iSup hFmono)
    simpa only [σ, μ, g, S, T] using hlim
