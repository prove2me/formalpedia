-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a415_original_inclusive_crossing_spatial_uniform_cell_modulus
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:43:16.819048+00:00
-- url     : https://prove2.me/submissions/e4fa58bb-2215-414e-ab38-dc69fc97f4bc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a414_zerojump_inclusive_crossing_subcell_raw_uniform_modulus
import Theorems.Thm_AvramDividend_Classical_avram_ga_a204_positive_compact_C2_source_small_raw_local_Lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_gledger137_original_gaussian_source_postpayment_compact_prefix_band
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
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∃ k : ℕ, ∀ m : ℕ, k ≤ m → ∀ i : ℕ, i < m →
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        s < ρ ω → ρ ω ≤ s + Δ →
          |Real.exp (-(q * (ρ ω : ℝ))) *
            (w (x + X.X (ρ ω) ω - rightLimit D s ω) -
             w (x + X.X s ω - rightLimit D s ω))| < ε := by
  let a : ℝ := 1 / ((j : ℝ) + 1)
  let b : ℝ := x + ((j : ℝ) + 1)
  have ha : 0 < a := by dsimp [a]; positivity
  have hDen : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have ha1 : a ≤ 1 := by
    dsimp [a]
    exact (div_le_iff₀ hDen).2 (by nlinarith [Nat.cast_nonneg (α := ℝ) j])
  have hb1 : 1 ≤ b := by
    dsimp [b]
    nlinarith [Nat.cast_nonneg (α := ℝ) j]
  have hab : a ≤ b := le_trans ha1 hb1
  have hSub : {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} = Ioi (0 : ℝ) := by
    ext y
    simp [hTopCap]
  have hwPos : ContDiffOn ℝ 2 w (Ioi (0 : ℝ)) := by
    simpa only [hSub] using hw_smooth
  obtain ⟨L,hL,hLip⟩ :=
    avram_ga_a204_positive_compact_C2_source_small_raw_local_Lipschitz
      w hwPos a b ha hab
  have hBand := avram_gledger137_original_gaussian_source_postpayment_compact_prefix_band
    X x D hD.1.1 ρ j hprefix
  have hRaw := avram_ga_a414_zerojump_inclusive_crossing_subcell_raw_uniform_modulus
    X hNuZero n ρ
  filter_upwards [hBand, hRaw] with ω hω hmod
  intro ε hε
  let η : ℝ := min (a / 2) (ε / (L + 1))
  have hη : 0 < η :=
    lt_min (half_pos ha) (div_pos hε (by linarith))
  obtain ⟨k, hk⟩ := hmod η hη
  refine ⟨k, ?_⟩
  intro m hm i hi Δ s hs ht
  let r : ℝ := X.X (ρ ω) ω - X.X s ω
  let y : ℝ := x + X.X s ω - rightLimit D s ω
  have hr : |r| < η := by
    simpa only [r, s, Δ] using hk m hm i hi hs ht
  have hsmall : |r| < a / 2 := lt_of_lt_of_le hr (min_le_left _ _)
  have hy : y ∈ Icc a b := hω s hs
  have hLoc := hLip y hy r hsmall
  have hE0 : 0 ≤ Real.exp (-(q * (ρ ω : ℝ))) := Real.exp_nonneg _
  have hE1 : Real.exp (-(q * (ρ ω : ℝ))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have hρ : (0 : ℝ) ≤ (ρ ω : ℝ) := (ρ ω).property
    nlinarith [mul_nonneg (le_of_lt hq) hρ]
  have hden : 0 < L + 1 := by linarith
  have hLast : L * (ε / (L + 1)) < ε := by
    rw [show L * (ε / (L + 1)) = L * ε / (L + 1) by ring]
    exact (div_lt_iff₀ hden).2 (by nlinarith)
  have hVal : |Real.exp (-(q * (ρ ω : ℝ))) * (w (y + r) - w y)| < ε := by
    calc
      _ = Real.exp (-(q * (ρ ω : ℝ))) * |w (y + r) - w y| := by
        rw [abs_mul, abs_of_nonneg hE0]
      _ ≤ |w (y + r) - w y| :=
        mul_le_of_le_one_left (abs_nonneg _) hE1
      _ ≤ L * |r| := hLoc
      _ ≤ L * η := mul_le_mul_of_nonneg_left (le_of_lt hr) hL
      _ ≤ L * (ε / (L + 1)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hL
      _ < ε := hLast
  have heq : y + r = x + X.X (ρ ω) ω - rightLimit D s ω := by
    dsimp [y, r]
    ring
  simpa only [heq, y, s, Δ] using hVal
