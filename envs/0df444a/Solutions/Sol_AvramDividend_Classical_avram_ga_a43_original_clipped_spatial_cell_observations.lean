-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a43_original_clipped_spatial_cell_observations
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T13:13:33.159204+00:00
-- url     : https://prove2.me/submissions/80976b48-e38f-417a-9a7c-7c66f715f593

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger20_original_strict_prefix_postpayment_floor
import Theorems.Thm_AvramDividend_Classical_avram_gledger54_original_stopped_source_cell_prepayment_floor
import Theorems.Thm_AvramDividend_Classical_avram_gledger67_original_clipped_gaussian_mesh_stops_measurable
import Theorems.Thm_AvramDividend_Classical_avram_gledger70_original_stopped_source_inactive_cell_zero
import Theorems.Thm_AvramDividend_Classical_avram_gledger74_measurable_original_clipped_NNReal_clock_to_real
import Theorems.Thm_AvramDividend_Classical_avram_gledger75_original_stopped_levy_and_rightDividend_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_gledger76_positive_only_value_masked_physical_source_measurable
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option maxHeartbeats 800000

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
    (ρ : Ω → ℝ≥0) (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    ∀ m : ℕ,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → Ω → ℝ≥0 := fun i ω => min ((i : ℝ≥0) * Δ) (ρ ω)
      let E : ℕ → Ω → ℝ := fun i ω => Real.exp (-(q * (v i ω : ℝ)))
      let Y : ℕ → Ω → ℝ := fun i ω => x + X.X (v i ω) ω - rightLimit D (v i ω) ω
      let Z : ℕ → Ω → ℝ := fun i ω => x + X.X (v (i + 1) ω) ω - rightLimit D (v i ω) ω
      (∀ i : ℕ, Measurable (E i)) ∧
      (∀ i : ℕ, Measurable (Y i)) ∧
      (∀ i : ℕ, Measurable (Z i)) ∧
      (∀ᵐ ω ∂P, ∀ i ∈ Finset.range (m + 1),
        (E (i + 1) ω = E i ω ∧ Z i ω = Y i ω) ∨
        (0 < Y i ω ∧ 0 < Z i ω)) := by
  intro m Δ v E Y Z
  have hDstrat : IsDividendStrategy 𝓕 D := hD.1.1
  have hρtop : Measurable (fun ω : Ω => (ρ ω : WithTop ℝ≥0)) :=
    hρstop.measurable.mono hρstop.measurableSpace_le le_rfl
  have hτbound (ω : Ω) : τ ω ≤ (n : ℝ≥0) := by
    rw [hτeq ω]
    have hm := min_le_right (ruinTime X x D ω) (n : ℝ≥0∞)
    have hnfinite : (n : ℝ≥0∞) ≠ ⊤ := by simp
    simpa using ENNReal.toNNReal_mono hnfinite hm
  have hρbound (ω : Ω) : ρ ω ≤ (n : ℝ≥0) := (hρle ω).trans (hτbound ω)
  have ht := avram_gledger67_original_clipped_gaussian_mesh_stops_measurable
    ρ hρstop n m hρbound
  have hObs :=
    avram_gledger75_original_stopped_levy_and_rightDividend_joint_measurable
      X hX D hDstrat ρ hρstop Δ
  have hvreal (i : ℕ) : Measurable (fun ω => (v i ω : ℝ)) := by
    simpa [v] using
      (avram_gledger74_measurable_original_clipped_NNReal_clock_to_real
        ρ hρtop ((i : ℝ≥0) * Δ))
  have hvstop (i : ℕ) : IsStoppingTime 𝓕.rightCont
      (fun ω => (v i ω : WithTop ℝ≥0)) := by
    have hs := hρstop.min_const ((i : ℝ≥0) * Δ)
    convert hs using 1
    funext ω
    simp [v, min_comm]
  have hY (i : ℕ) : Measurable (Y i) := by
    dsimp [Y]
    exact (measurable_const.add (hObs i).1).sub (hObs i).2
  have hZ (i : ℕ) : Measurable (Z i) := by
    dsimp [Z]
    exact (measurable_const.add (hObs (i + 1)).1).sub (hObs i).2
  have hE (i : ℕ) : Measurable (E i) := by
    dsimp [E]
    exact Real.measurable_exp.comp ((measurable_const.mul (hvreal i)).neg)
  have hwcont : ContinuousOn w (Ioi (0 : ℝ)) := by
    apply hw_smooth.continuousOn.mono
    intro y hy
    exact ⟨hy, by simp [hTopCap]⟩
  have hz := avram_gledger54_original_stopped_source_cell_prepayment_floor
    X hNuZero x D hDstrat ρ j n m hn hprefix
  have hcell : ∀ᵐ ω ∂P, ∀ i ∈ Finset.range (m + 1),
      (E (i + 1) ω = E i ω ∧ Z i ω = Y i ω) ∨
      (0 < Y i ω ∧ 0 < Z i ω) := by
    filter_upwards [hprefix, hz] with ω hp hpz
    intro i hi
    let s : ℝ≥0 := (i : ℝ≥0) * Δ
    by_cases hstop : ρ ω ≤ s
    · left
      have hzero := avram_gledger70_original_stopped_source_inactive_cell_zero
        Δ i (ρ ω) q x (fun t => X.X t ω)
        (fun t => rightLimit D t ω) hstop
      simpa only [v, E, Y, Z, s] using hzero
    · right
      have hs : s < ρ ω := lt_of_not_ge hstop
      have hv : v i ω = s := min_eq_left (le_of_lt hs)
      let u : ℝ := (1 : ℝ) / ((j : ℝ) + 1)
      have hu : 0 < u := by dsimp [u]; positivity
      have hy := avram_gledger20_original_strict_prefix_postpayment_floor
        X x D hDstrat ω (ρ ω) u
        (fun t ht htρ => (hp t ht htρ).1) s hs
      have hypos : 0 < Y i ω :=
        lt_of_lt_of_le hu (by simpa [Y, v, hv, s, u] using hy)
      have hz0 := hpz i hi hs
      have hzpos : 0 < Z i ω :=
        lt_of_lt_of_le hu (by simpa [Z, v, hv, s, u] using hz0)
      exact ⟨hypos, hzpos⟩
  exact ⟨hE, hY, hZ, hcell⟩
