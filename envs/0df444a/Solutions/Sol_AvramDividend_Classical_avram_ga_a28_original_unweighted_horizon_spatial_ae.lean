-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a28_original_unweighted_horizon_spatial_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T22:04:55.249189+00:00
-- url     : https://prove2.me/submissions/1956672e-d1e2-4a1c-92dd-6f020b09086b

import Theorems.Thm_AvramDividend_Classical_avram_gledger137_original_gaussian_source_postpayment_compact_prefix_band
import Theorems.Thm_AvramDividend_Classical_avram_ga_a27_original_path_terminal_increment_ae
import Theorems.Thm_AvramDividend_Classical_avram_ga_a27_prehorizon_grid_le
import Theorems.Thm_AvramDividend_Classical_avram_ga_a27_horizon_clipped_endpoint
import Theorems.Thm_AvramDividend_Classical_avram_ga_a28_compact_modulus_last_increment
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hSigmaNonzero : X.σ ≠ 0) (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let S : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      w (Z m) - w (Y (v m))
    ∀ᵐ ω ∂P, (n : ℝ≥0) ≤ ρ ω → Tendsto (fun m => S m ω) atTop (nhds (0 : ℝ)) := by
  classical
  dsimp only
  have hInc := avram_ga_a27_original_path_terminal_increment_ae X hNuZero (n : ℝ≥0)
  have hPost := avram_gledger137_original_gaussian_source_postpayment_compact_prefix_band
    X x D hD.1.1 ρ j hprefix
  filter_upwards [hPost, hInc] with ω hBand hIncrement
  intro hρ
  let n0 : ℝ≥0 := n
  let u : ℕ → ℝ≥0 := fun m => (m : ℝ≥0) * (n0 / ((m : ℝ≥0) + 1))
  let y : ℕ → ℝ := fun m => x + X.X (u m) ω - rightLimit D (u m) ω
  let z : ℕ → ℝ := fun m => x + X.X n0 ω - rightLimit D (u m) ω
  have hVm (m : ℕ) : min (u m) (ρ ω) = u m :=
    min_eq_left ((avram_ga_a27_prehorizon_grid_le n0 m).trans hρ)
  have hVS (m : ℕ) :
      min (((m + 1 : ℕ) : ℝ≥0) *
        (n0 / ((m : ℝ≥0) + 1))) (ρ ω) = n0 :=
    avram_ga_a27_horizon_clipped_endpoint n0 m (ρ ω) hρ
  have hd : Tendsto (fun m => z m - y m)
      atTop (nhds (0 : ℝ)) := by
    have heq : (fun m => z m - y m) = (fun m => X.X n0 ω - X.X (u m) ω) := by
      funext m
      dsimp [z, y]; ring
    rw [heq]; simpa [n0, u] using hIncrement
  have hn0 : 0 < n0 := Nat.cast_pos.mpr hn
  have huLt (m : ℕ) : u m < n0 := by
    dsimp [u]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (show 0 < (m : ℝ≥0) + 1 by positivity)).mpr
    nlinarith [hn0]
  let a0 : ℝ := 1 / ((j : ℝ) + 1)
  let b0 : ℝ := x + ((j : ℝ) + 1)
  let a : ℝ := a0 / 2
  let b : ℝ := b0 + 1
  have hLower : 0 < a := by dsimp [a, a0]; positivity
  have hyStrong : ∀ᶠ m in atTop, y m ∈ Set.Icc a0 b0 := by
    filter_upwards [Filter.Eventually.of_forall
      (fun m => hBand (u m) ((huLt m).trans_le hρ))] with m ht
    simpa [Set.mem_Icc, y, a0, b0] using ht
  have hy : ∀ᶠ m in atTop, y m ∈ Set.Icc a b := by
    filter_upwards [hyStrong] with m hm
    have ha : a ≤ a0 := by dsimp [a] at hLower ⊢; linarith
    exact ⟨ha.trans hm.1, by dsimp [b]; linarith [hm.2]⟩
  have hCont : ContinuousOn w (Set.Icc a b) := by
    apply hw_smooth.continuousOn.mono
    intro v hv; change 0 < v ∧ ENNReal.ofReal v < C
    exact ⟨hLower.trans_le hv.1, by simp [hTopCap]⟩
  have hUC : UniformContinuousOn w (Set.Icc a b) := isCompact_Icc.uniformContinuousOn_of_continuous hCont
  have hmod : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ v t : ℝ, v ∈ Set.Icc a b → t ∈ Set.Icc a b →
      |t - v| < δ → |w t - w v| < ε := by
    intro ε hε
    obtain ⟨δ, hδ, hh⟩ := Metric.uniformContinuousOn_iff.mp hUC ε hε
    refine ⟨δ, hδ, ?_⟩
    intro v t hv ht hdist
    have hdist' : dist v t < δ := by simpa [Real.dist_eq, abs_sub_comm] using hdist
    simpa [Real.dist_eq, abs_sub_comm] using hh v hv t ht hdist'
  have hSmall : ∀ᶠ m in atTop, |z m - y m| < min a 1 := by
    have hs : 0 < min a 1 := lt_min hLower (by norm_num)
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hd) (min a 1) hs
    filter_upwards [eventually_ge_atTop N] with m hm
    simpa [Real.dist_eq] using hN m hm
  have hz : ∀ᶠ m in atTop, z m ∈ Set.Icc a b := by
    filter_upwards [hyStrong, hSmall] with m hm hs
    have hlo : 2 * a = a0 := by dsimp [a]; ring
    constructor
    · linarith [(abs_lt.mp hs).1, min_le_left a 1, hm.1]
    · dsimp [b]
      linarith [(abs_lt.mp hs).2, min_le_right a 1, hm.2]
  have hConv := avram_ga_a28_compact_modulus_last_increment w a b y z hmod hy hz hd
  convert hConv using 1
  funext m
  dsimp [y, z, u, n0]; rw [hVm m, hVS m]
