-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a41b_original_terminal_cell_exponential_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T15:59:22.350049+00:00
-- url     : https://prove2.me/submissions/80734fd6-d1cf-4f1a-9367-f815635f97ed

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ga_a45_original_uniform_clipped_source_active_cell_envelope
import Theorems.Thm_AvramDividend_Classical_avram_ga_a44_discounted_terminal_spatial_positive_sup_bound
import Theorems.Thm_AvramDividend_Classical_avram_ga_a34_original_clipped_source_le_runningSup
import Theorems.Thm_AvramDividend_Classical_avram_ga_a35_original_dividend_rightLimit_nonnegative
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hSigmaNonzero : X.σ ≠ 0)
    (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0) (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (ρ : Ω → ℝ≥0) (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0))) (hρle : ∀ ω, ρ ω ≤ τ ω) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω → (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧ riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let Last : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      E (v (m + 1)) * (w (Z m) - w (Y (v m)))
    let F : ℕ → Ω → ℝ := fun m ω =>
      if 0 < ρ ω then max (Last m ω) (0 : ℝ) else 0
    ∃ theta K L : ℝ, 0 ≤ theta ∧ 0 ≤ K ∧ 0 ≤ L ∧ ∀ m : ℕ, ∀ᵐ ω ∂P, ‖F m ω‖ ≤ K * Real.exp (theta * runningSup X (n : ℝ≥0) ω) + L := by
  classical
  intro Last F
  obtain ⟨ θ, K, b, hθ, hK, hb, hCellsAll ⟩ :=
    avram_ga_a45_original_uniform_clipped_source_active_cell_envelope
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix
  refine ⟨ θ, K * Real.exp (θ * x), b, hθ, ?_, hb, ?_ ⟩
  · exact mul_nonneg hK (le_of_lt (Real.exp_pos _))
  · intro m
    let Delta : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : Nat → Ω → ℝ≥0 := fun i omega => min ((i : ℝ≥0) * Delta) (ρ omega)
    let E : Nat → Ω → ℝ := fun i omega => Real.exp (-(q * (v i omega : ℝ)))
    let Y : Nat → Ω → ℝ := fun i omega => x + X.X (v i omega) omega - rightLimit D (v i omega) omega
    let Z : Nat → Ω → ℝ := fun i omega => x + X.X (v (i + 1) omega) omega - rightLimit D (v i omega) omega
    have hτbound (omega : Ω) : τ omega ≤ (n : ℝ≥0) := by
      rw [hτeq omega]
      have hm := min_le_right (ruinTime X x D omega) (n : ℝ≥0∞)
      have hnfinite : (n : ℝ≥0∞) ≠ ⊤ := by simp
      simpa using ENNReal.toNNReal_mono hnfinite hm
    have hρbound (omega : Ω) : ρ omega ≤ (n : ℝ≥0) := (hρle omega).trans (hτbound omega)
    have hD0 : ∀ (t : ℝ≥0) (omega : Ω), 0 ≤ rightLimit D t omega := avram_ga_a35_original_dividend_rightLimit_nonnegative D hD.1.1
    have hZceil (omega : Ω) : Z m omega ≤ x + runningSup X (n : ℝ≥0) omega := by
      simpa [Z, v, Delta] using (avram_ga_a34_original_clipped_source_le_runningSup X x D hD0 (n : ℝ≥0) ρ hρbound m omega)
    have hSource := hCellsAll m
    change (∀ᵐ omega ∂ P, ∀ i ∈ Finset.range (m + 1), (E (i + 1) omega = E i omega ∧ Z i omega = Y i omega) ∨ (-b ≤ w (Y i omega) ∧ w (Z i omega) ≤ K * Real.exp (θ * Z i omega))) at hSource
    have hLastCells : ∀ᵐ omega ∂ P, (Z m omega = Y m omega) ∨ (-b ≤ w (Y m omega) ∧ w (Z m omega) ≤ K * Real.exp (θ * Z m omega) ∧ Z m omega ≤ x + runningSup X (n : ℝ≥0) omega) := by
      filter_upwards [hSource] with omega hc
      rcases hc m (Finset.mem_range.mpr (Nat.lt_succ_self m)) with hl | hr
      · exact Or.inl hl.2
      · exact Or.inr ⟨ hr.1, hr.2, hZceil omega ⟩
    have hMajor := avram_ga_a44_discounted_terminal_spatial_positive_sup_bound q θ K b (le_of_lt hq) hθ hK hb (fun omega => v (m + 1) omega) w (Y m) (Z m) (fun omega => x + runningSup X (n : ℝ≥0) omega) hLastCells
    filter_upwards [hMajor] with omega hg
    have hUpper : 0 ≤
        (K * Real.exp (θ * x)) *
          Real.exp (θ * runningSup X (n : ℝ≥0) omega) + b :=
      add_nonneg
        (mul_nonneg (mul_nonneg hK (le_of_lt (Real.exp_pos _)))
          (le_of_lt (Real.exp_pos _))) hb
    by_cases hρpos : 0 < ρ omega
    · have hF : F m omega = max (Real.exp (-(q * (v (m + 1) omega : ℝ))) * (w (Z m omega) - w (Y m omega))) (0 : ℝ) := by simp [F, Last, E, Y, Z, v, Delta, hρpos]
      have hFnonneg : 0 ≤ F m omega := by
        simp [hF]
      calc
        norm (F m omega) = F m omega := by
          simpa only [Real.norm_eq_abs] using (abs_of_nonneg hFnonneg)
        _ = _ := hF
        _ ≤ K * Real.exp (θ * (x + runningSup X (n : ℝ≥0) omega)) + b := hg
        _ = (K * Real.exp (θ * x)) * Real.exp (θ * runningSup X (n : ℝ≥0) omega) + b := by
              rw [mul_add, Real.exp_add]
              ring
    · have hFzero : F m omega = 0 := by simp [F, hρpos]
      simpa [hFzero] using hUpper
