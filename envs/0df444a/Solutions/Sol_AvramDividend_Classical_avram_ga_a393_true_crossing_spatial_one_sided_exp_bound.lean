-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a393_true_crossing_spatial_one_sided_exp_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T16:43:02.509134+00:00
-- url     : https://prove2.me/submissions/1516867e-9cbb-4add-bf0c-234d5061fd62

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ga_a45_original_uniform_clipped_source_active_cell_envelope
import Theorems.Thm_AvramDividend_Classical_avram_ga_a33_terminal_positive_exponential_majorant
import Theorems.Thm_AvramDividend_Classical_avram_ga_a35_original_dividend_rightLimit_nonnegative
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
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
    ∃ θ K b : ℝ, 0 ≤ θ ∧ 0 ≤ K ∧ 0 ≤ b ∧
      ∀ (m : ℕ), ∀ᵐ ω ∂P, ∀ (i : ℕ), i < m →
        (i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) < ρ ω →
        ρ ω < ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) +
          (n : ℝ≥0) / ((m : ℝ≥0) + 1)) →
        max (Real.exp (-(q * (ρ ω : ℝ))) *
          (w (x + X.X (ρ ω) ω -
              rightLimit D ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω) -
           w (x + X.X ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω -
              rightLimit D ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω))) 0 ≤
          K * Real.exp (θ * runningSup X (n : ℝ≥0) ω) + b := by
  classical
  obtain ⟨θ, K, b, hθ, hK, hb, hCellsAll⟩ :=
    avram_ga_a45_original_uniform_clipped_source_active_cell_envelope
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix
  refine ⟨θ, K * Real.exp (θ * x), b, hθ,
    mul_nonneg hK (le_of_lt (Real.exp_pos _)), hb, ?_⟩
  intro m
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let v : ℕ → Ω → ℝ≥0 := fun i ω => min ((i : ℝ≥0) * Δ) (ρ ω)
  let E : ℕ → Ω → ℝ := fun i ω => Real.exp (-(q * (v i ω : ℝ)))
  let Y : ℕ → Ω → ℝ := fun i ω => x + X.X (v i ω) ω - rightLimit D (v i ω) ω
  let Z : ℕ → Ω → ℝ := fun i ω => x + X.X (v (i + 1) ω) ω - rightLimit D (v i ω) ω
  have hCells := hCellsAll m
  change ∀ᵐ ω ∂P, ∀ i ∈ Finset.range (m + 1),
    (E (i + 1) ω = E i ω ∧ Z i ω = Y i ω) ∨
      (-b ≤ w (Y i ω) ∧
        w (Z i ω) ≤ K * Real.exp (θ * Z i ω)) at hCells
  have hτbound (ω : Ω) : τ ω ≤ (n : ℝ≥0) := by
    rw [hτeq ω]
    simpa using ENNReal.toNNReal_mono (by simp : (n : ℝ≥0∞) ≠ ⊤)
      (min_le_right (ruinTime X x D ω) (n : ℝ≥0∞))
  have hρbound (ω : Ω) : ρ ω ≤ (n : ℝ≥0) := (hρle ω).trans (hτbound ω)
  have hD0 := avram_ga_a35_original_dividend_rightLimit_nonnegative D hD.1.1
  filter_upwards [hCells] with ω hc
  intro i hi hs ht
  let si : ℝ≥0 := (i : ℝ≥0) * Δ
  have hvi : v i ω = si := min_eq_left (le_of_lt hs)
  have hstep : ((i + 1 : ℕ) : ℝ≥0) * Δ = si + Δ := by
    dsimp [si]; rw [Nat.cast_succ, add_mul, one_mul]
  have hvip : v (i + 1) ω = ρ ω := by
    dsimp [v]; rw [hstep]
    exact min_eq_right (le_of_lt ht)
  have hXceil : X.X (ρ ω) ω ≤ runningSup X (n : ℝ≥0) ω :=
    ((runningSup_monotone_and_path_le X ω).2 (ρ ω)).trans
      ((runningSup_monotone_and_path_le X ω).1 (hρbound ω))
  have hZceil : Z i ω ≤ x + runningSup X (n : ℝ≥0) ω := by
    dsimp [Z]; rw [hvi, hvip]
    have hd := hD0 si ω
    linarith only [hXceil, hd]
  have hBound : max (E (i+1) ω *
      (w (Z i ω) - w (Y i ω))) 0 ≤
      K * Real.exp (θ * (x + runningSup X (n : ℝ≥0) ω)) + b := by
    rcases hc i (Finset.mem_range.mpr (hi.trans (Nat.lt_succ_self m)))
      with hz | ⟨hlo,hup⟩
    · have hR := add_nonneg
        (mul_nonneg hK (le_of_lt (Real.exp_pos (θ * (x + runningSup X n ω))))) hb
      simpa [hz] using hR
    · have hBase :=
        avram_ga_a33_terminal_positive_exponential_majorant
          q θ K b (le_of_lt hq) hK hb
          (v (i+1) ω) (w (Z i ω)) (w (Y i ω))
          (Z i ω) hlo hup
      have hExp := (Real.exp_le_exp).2
        (mul_le_mul_of_nonneg_left hZceil hθ)
      exact hBase.trans (by
        nlinarith only [mul_le_mul_of_nonneg_left hExp hK])
  have hEq :
      Real.exp (-(q * (ρ ω : ℝ))) *
        (w (x + X.X (ρ ω) ω - rightLimit D si ω) -
          w (x + X.X si ω - rightLimit D si ω)) =
      E (i+1) ω * (w (Z i ω) - w (Y i ω)) := by
    dsimp [E, Y, Z]
    rw [hvi, hvip]
  rw [← hEq] at hBound
  rw [mul_add, Real.exp_add] at hBound
  simpa [si, Δ, mul_assoc, mul_left_comm, mul_comm] using hBound
