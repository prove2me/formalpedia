-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a45_original_uniform_clipped_source_active_cell_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T15:56:14.706263+00:00
-- url     : https://prove2.me/submissions/ad246897-61e5-4003-921e-97d1eaba00e6

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger20_original_strict_prefix_postpayment_floor
import Theorems.Thm_AvramDividend_Classical_avram_gledger54_original_stopped_source_cell_prepayment_floor
import Theorems.Thm_AvramDividend_Classical_avram_gledger63_compact_continuous_value_finite_lower_bound
import Theorems.Thm_AvramDividend_Classical_avram_gledger65_original_topcap_HJB_positive_halfline_exponential_upper
import Theorems.Thm_AvramDividend_Classical_avram_gledger70_original_stopped_source_inactive_cell_zero
import Theorems.Thm_AvramDividend_Classical_riskProcess_tendsto_postPaymentReserve_right
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Active physical cells carry a compact postpayment lower band and an
    exponential prepayment upper bound; inactive cells contribute zero. -/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hSigmaNonzero : X.σ ≠ 0)
    (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω)
    (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    ∃ θ K b : ℝ, 0 ≤ θ ∧ 0 ≤ K ∧ 0 ≤ b ∧
    ∀ m : ℕ,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → Ω → ℝ≥0 := fun i ω => min ((i : ℝ≥0) * Δ) (ρ ω)
      let E : ℕ → Ω → ℝ := fun i ω => Real.exp (-(q * (v i ω : ℝ)))
      let Y : ℕ → Ω → ℝ := fun i ω =>
        x + X.X (v i ω) ω - rightLimit D (v i ω) ω
      let Z : ℕ → Ω → ℝ := fun i ω =>
        x + X.X (v (i + 1) ω) ω - rightLimit D (v i ω) ω
      let S : Ω → ℝ := fun ω => Finset.sum (Finset.range (m + 1)) (fun i =>
        (E (i + 1) ω - E i ω) * w (Y i ω) +
        E (i + 1) ω * (w (Z i ω) - w (Y i ω)))
      (∀ᵐ ω ∂P, ∀ i ∈ Finset.range (m + 1),
          (E (i + 1) ω = E i ω ∧ Z i ω = Y i ω) ∨
          (-b ≤ w (Y i ω) ∧
            w (Z i ω) ≤ K * Real.exp (θ * Z i ω))) := by
  let u : ℝ := 1 / ((j : ℝ) + 1)
  let b₀ : ℝ := x + ((j : ℝ) + 1)
  let a : ℝ := min u b₀
  have hu : 0 < u := by dsimp [u]; positivity
  have hb₀ : 0 < b₀ := by dsimp [b₀]; positivity
  have ha : 0 < a := lt_min hu hb₀
  have hab : a ≤ b₀ := min_le_right _ _
  have hsub : Icc a b₀ ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    intro y hy
    exact ⟨lt_of_lt_of_le ha hy.1, by simp [hTopCap]⟩
  have hcont : ContinuousOn w (Icc a b₀) :=
    hw_smooth.continuousOn.mono hsub
  obtain ⟨b, hb, hlow⟩ :=
    avram_gledger63_compact_continuous_value_finite_lower_bound
      a b₀ hab w hcont
  obtain ⟨θ, K, hθ, hK, hupper⟩ :=
    avram_gledger65_original_topcap_HJB_positive_halfline_exponential_upper
      X hNuZero hSigmaNonzero q hq w C hTopCap
      hw_smooth hw_gen a ha
  refine ⟨θ, K, b, hθ, hK, hb, ?_⟩
  intro m Δ v E Y Z S
  have hz :=
    avram_gledger54_original_stopped_source_cell_prepayment_floor
      X hNuZero x D hD.1.1 ρ j n m hn hprefix
  filter_upwards [hprefix, hz] with ω hp hpz
  intro i hi
  let s : ℝ≥0 := (i : ℝ≥0) * Δ
  by_cases hstop : ρ ω ≤ s
  · left
    have hz0 :=
      avram_gledger70_original_stopped_source_inactive_cell_zero
        Δ i (ρ ω) q x (fun t => X.X t ω)
        (fun t => rightLimit D t ω) hstop
    simpa only [v, E, Y, Z, s] using hz0
  · right
    have hs : s < ρ ω := lt_of_not_ge hstop
    have hv : v i ω = s := min_eq_left (le_of_lt hs)
    have hylo : a ≤ Y i ω := by
      have hp0 := avram_gledger20_original_strict_prefix_postpayment_floor
        X x D hD.1.1 ω (ρ ω) u
        (fun t ht htρ => (hp t ht htρ).1) s hs
      exact (min_le_left u b₀).trans (by simpa [Y, hv] using hp0)
    have hyhi : Y i ω ≤ b₀ := by
      have hp1 : x + X.X s ω - rightLimit D s ω ≤ b₀ := by
        have hT := riskProcess_tendsto_postPaymentReserve_right
          X x D hD.1.1 ω s
        have hlt : ∀ᶠ t : ℝ≥0 in 𝓝[>] s, t < ρ ω :=
          (eventually_lt_nhds hs).filter_mono nhdsWithin_le_nhds
        have hgt : ∀ᶠ t : ℝ≥0 in 𝓝[>] s, s < t :=
          self_mem_nhdsWithin
        have hUpper : ∀ᶠ t : ℝ≥0 in 𝓝[>] s,
            riskProcess X x D t ω ≤ b₀ := by
          filter_upwards [hgt, hlt] with t hst htρ
          exact (hp t (lt_of_le_of_lt (by exact zero_le) hst) htρ).2
        exact le_of_tendsto hT hUpper
      simpa [Y, hv] using hp1
    have hzlo : a ≤ Z i ω := by
      have hz0 := hpz i hi hs
      have hz1 : u ≤ Z i ω := by
        simpa [Z, v, hv, s, u] using hz0
      exact (min_le_left u b₀).trans hz1
    exact ⟨hlow _ hylo hyhi, hupper _ hzlo⟩
