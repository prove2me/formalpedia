-- Prove2me | solution 1 for EliasGlobalClock.LowerBound.jensen_interval
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-10T21:26:29.052766+00:00
-- url     : https://prove2.me/submissions/885f22f5-df8d-4f73-9bdf-e410888a1b16

import Mathlib

open MeasureTheory

lemma jensen_aux_support (I : Set ℝ) (φ : ℝ → ℝ) (hc : ConvexOn ℝ I φ) (m : ℝ) (hm : m ∈ I)
    (hL : ∃ a ∈ I, a < m) (hR : ∃ b ∈ I, m < b) :
    ∃ c : ℝ, ∀ y ∈ I, φ m + c * (y - m) ≤ φ y := by
  obtain ⟨a0, ha0, ha0m⟩ := hL
  obtain ⟨b0, hb0, hb0m⟩ := hR
  set S : Set ℝ := {s | ∃ a ∈ I, a < m ∧ s = (φ m - φ a) / (m - a)} with hS
  have hne : S.Nonempty := ⟨_, a0, ha0, ha0m, rfl⟩
  have hub : ∀ b ∈ I, m < b → ∀ s ∈ S, s ≤ (φ b - φ m) / (b - m) := by
    rintro b hb hmb s ⟨a, ha, ham, rfl⟩
    have := hc.slope_mono_adjacent ha hb ham hmb
    exact this
  have hbdd : BddAbove S := ⟨_, hub b0 hb0 hb0m⟩
  refine ⟨sSup S, fun y hy => ?_⟩
  rcases lt_trichotomy y m with h | h | h
  · have h1 : (φ m - φ y) / (m - y) ≤ sSup S := le_csSup hbdd ⟨y, hy, h, rfl⟩
    rw [div_le_iff₀ (by linarith)] at h1
    nlinarith
  · subst h; simp
  · have h1 : sSup S ≤ (φ y - φ m) / (y - m) := csSup_le hne (hub y hy h)
    rw [le_div_iff₀ (by linarith)] at h1
    nlinarith

lemma jensen_aux {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (I : Set ℝ) (X : Ω → ℝ) (φ : ℝ → ℝ)
    (hX : Integrable X μ) (hXI : ∀ᵐ ω ∂μ, X ω ∈ I)
    (hm : (∫ ω, X ω ∂μ) ∈ I) (hφX : Integrable (fun ω => φ (X ω)) μ)
    (hc : ConvexOn ℝ I φ) : φ (∫ ω, X ω ∂μ) ≤ ∫ ω, φ (X ω) ∂μ := by
  set m := ∫ ω, X ω ∂μ with hmdef
  have degen : (∀ᵐ ω ∂μ, X ω = m) → φ m ≤ ∫ ω, φ (X ω) ∂μ := by
    intro h
    have : ∫ ω, φ (X ω) ∂μ = ∫ _ω, φ m ∂μ := integral_congr_ae (by
      filter_upwards [h] with ω hω; rw [hω])
    rw [this]; simp
  by_cases hL : ∃ a ∈ I, a < m
  · by_cases hR : ∃ b ∈ I, m < b
    · obtain ⟨c, hcc⟩ := jensen_aux_support I φ hc m hm hL hR
      have hi : Integrable (fun ω => c * (X ω - m)) μ := (hX.sub (integrable_const m)).const_mul c
      have h1 : ∫ ω, (φ m + c * (X ω - m)) ∂μ ≤ ∫ ω, φ (X ω) ∂μ := by
        apply integral_mono_ae
        · exact (integrable_const _).add hi
        · exact hφX
        · filter_upwards [hXI] with ω hω using hcc _ hω
      have h2 : ∫ ω, (φ m + c * (X ω - m)) ∂μ = φ m := by
        rw [integral_add (integrable_const _) hi,
          integral_const_mul, integral_sub hX (integrable_const m)]
        simp [hmdef]
      linarith
    · apply degen
      have hle : ∀ᵐ ω ∂μ, X ω ≤ m := by
        filter_upwards [hXI] with ω hω
        by_contra h; exact hR ⟨_, hω, not_le.mp h⟩
      have h0 : ∫ ω, (m - X ω) ∂μ = 0 := by
        rw [integral_sub (integrable_const m) hX]; simp [hmdef]
      have := (integral_eq_zero_iff_of_nonneg_ae (by
        filter_upwards [hle] with ω hω using sub_nonneg.mpr hω)
        ((integrable_const m).sub hX)).mp h0
      filter_upwards [this] with ω hω
      have hω' : m - X ω = 0 := hω
      linarith
  · apply degen
    have hle : ∀ᵐ ω ∂μ, m ≤ X ω := by
      filter_upwards [hXI] with ω hω
      by_contra h; exact hL ⟨_, hω, not_le.mp h⟩
    have h0 : ∫ ω, (X ω - m) ∂μ = 0 := by
      rw [integral_sub hX (integrable_const m)]; simp [hmdef]
    have := (integral_eq_zero_iff_of_nonneg_ae (by
      filter_upwards [hle] with ω hω using sub_nonneg.mpr hω)
      (hX.sub (integrable_const m))).mp h0
    filter_upwards [this] with ω hω
    have hω' : X ω - m = 0 := hω
    linarith

/-- Fact D.1, printed p.36 / PDF p.37. No continuity or closedness assumption.
ConvexOn/ConcaveOn include convexity of I, hence precisely the interval condition
in one real dimension. The extension of φ outside I is immaterial almost surely. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (I : Set ℝ) (X : Ω → ℝ) (φ : ℝ → ℝ)
    (hX : Integrable X μ) (hXI : ∀ᵐ ω ∂μ, X ω ∈ I)
    (hm : (∫ ω, X ω ∂μ) ∈ I) (hφX : Integrable (fun ω => φ (X ω)) μ) :
    (ConvexOn ℝ I φ → φ (∫ ω, X ω ∂μ) ≤ ∫ ω, φ (X ω) ∂μ) ∧
    (ConcaveOn ℝ I φ → (∫ ω, φ (X ω) ∂μ) ≤ φ (∫ ω, X ω ∂μ)) := by
  refine ⟨fun hc => jensen_aux μ I X φ hX hXI hm hφX hc, fun hc => ?_⟩
  have := jensen_aux μ I X (fun x => -φ x) hX hXI hm hφX.neg hc.neg
  rw [integral_neg] at this
  linarith
