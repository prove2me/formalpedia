-- Prove2me | solution 1 for FiniteEnergyPlane.exists_abs_aCoord_le_of_tendsto_loopAction_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-26T20:53:10.209912+00:00
-- url     : https://prove2.me/submissions/02992101-7b48-46b2-bb49-9d389550819d

import Definitions.Def_FiniteEnergyPlane_Setting
import Theorems.Thm_FiniteEnergyPlane_abs_aCoord_sub_le_of_norm_eq
import Theorems.Thm_FiniteEnergyPlane_lintegral_energyDensity_annulus_le_loopAction
import Theorems.Thm_FiniteEnergyPlane_exists_pos_le_lintegral_energyDensity_annulus



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem exists_abs_aCoord_le_of_tendsto_loopAction_zero_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u)
    (hG : ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ z : ℂ, z ≠ 0 → ‖z‖ < r → ‖z‖ * gradNorm H u z ≤ C)
    (hQ : Tendsto (fun ρ => loopAction H u (cwLoop 0 ρ)) (𝓝[>] 0) (𝓝 0)) :
    ∃ r : ℝ, 0 < r ∧ ∃ A : ℝ, ∀ z : ℂ, z ≠ 0 → ‖z‖ < r → |aCoord H (u z)| ≤ A := by
  obtain ⟨r, hr, C, hC⟩ := hG
  obtain ⟨c, hc, hL⟩ := exists_pos_le_lintegral_energyDensity_annulus H hH J hJ u hu
  set a : ℂ → ℝ := fun z => aCoord H (u z) with hadef
  set Q : ℝ → ℝ := fun ρ => loopAction H u (cwLoop 0 ρ) with hQdef
  -- small loop actions
  obtain ⟨δ, hδ, hδQ⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < δ → |Q ρ| < c / 2 := by
    have := (Metric.tendsto_nhds.1 hQ) (c / 2) (by linarith)
    rcases (eventually_nhdsWithin_iff.1 this |> Metric.eventually_nhds_iff.1) with ⟨δ, hδ, h⟩
    refine ⟨δ, hδ, fun ρ h0 h1 => ?_⟩
    have := h (by rw [Real.dist_eq, sub_zero, abs_of_pos h0]; exact h1) h0
    simpa [Real.dist_eq] using this
  set ρ₀ : ℝ := min (min r 1) δ / 2 with hρ₀def
  have hρ₀ : 0 < ρ₀ := by positivity
  have hρ₀r : ρ₀ < r := by
    have : min (min r 1) δ ≤ r := (min_le_left _ _).trans (min_le_left _ _)
    linarith
  have hρ₀1 : ρ₀ < 1 := by
    have : min (min r 1) δ ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
    linarith
  have hρ₀δ : ρ₀ < δ := by
    have : min (min r 1) δ ≤ δ := min_le_right _ _
    linarith
  set K : ℝ := 6 * π * C with hKdef
  -- oscillation on circles
  have hosc : ∀ z z' : ℂ, z ≠ 0 → ‖z‖ < ρ₀ ∨ ‖z‖ = ρ₀ → ‖z'‖ = ‖z‖ → |a z - a z'| ≤ K := by
    intro z z' hz hzρ hzz'
    have hzρ' : ‖z‖ ≤ ρ₀ := by rcases hzρ with h | h <;> [exact h.le; exact h.le]
    exact abs_aCoord_sub_le_of_norm_eq H hH J hJ u hu r C hC z z' hz (by linarith)
      (by linarith) hzz'
  set z₀ : ℂ := (ρ₀ : ℂ) with hz₀def
  have hz₀n : ‖z₀‖ = ρ₀ := by rw [hz₀def, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ₀]
  have hz₀ : z₀ ≠ 0 := by intro h; rw [h, norm_zero] at hz₀n; linarith
  refine ⟨ρ₀, hρ₀, |a z₀| + 2 * K + 2, ?_⟩
  intro z hz hzρ
  by_contra hcon
  push_neg at hcon
  set ρ₂ : ℝ := ‖z‖ with hρ₂def
  have hρ₂ : 0 < ρ₂ := norm_pos_iff.2 hz
  -- the two circles and the level
  have key : ∀ A : ℝ, (((∀ w : ℂ, ‖w‖ = ρ₀ → a w ≤ A) ∧ ∀ w : ℂ, ‖w‖ = ρ₂ → A + 1 ≤ a w) ∨
      ((∀ w : ℂ, ‖w‖ = ρ₀ → A + 1 ≤ a w) ∧ ∀ w : ℂ, ‖w‖ = ρ₂ → a w ≤ A)) → False := by
    intro A hA
    have h1 := hL A ρ₀ ρ₂ hρ₂ hzρ hρ₀1 hA
    have h2 := lintegral_energyDensity_annulus_le_loopAction H hH J hJ u hu A ρ₀ ρ₂ hρ₂ hzρ hρ₀1
      (by rcases hA with h | h; exacts [Or.inl h.1, Or.inr h.1])
      (by rcases hA with h | h; exacts [Or.inr h.2, Or.inl h.2])
    have hq0 := hδQ ρ₀ hρ₀ hρ₀δ
    have hq2 := hδQ ρ₂ hρ₂ (by linarith)
    have := h1.trans h2
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at this
    change c ≤ |Q ρ₀| + |Q ρ₂| at this
    linarith
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hosc z₀ z₀ hz₀ (Or.inr hz₀n) rfl)
  have hout : ∀ w : ℂ, ‖w‖ = ρ₀ → |a w - a z₀| ≤ K := by
    intro w hw
    rw [abs_sub_comm]; exact hosc z₀ w hz₀ (Or.inr hz₀n) (by rw [hw, hz₀n])
  have hin : ∀ w : ℂ, ‖w‖ = ρ₂ → |a w - a z| ≤ K := by
    intro w hw
    rw [abs_sub_comm]; exact hosc z w hz (Or.inl hzρ) hw
  rcases le_or_gt 0 (a z) with hpos | hneg
  · rw [abs_of_nonneg hpos] at hcon
    refine key (a z₀ + K) (Or.inl ⟨fun w hw => ?_, fun w hw => ?_⟩)
    · have := hout w hw; rw [abs_le] at this; linarith
    · have := hin w hw; rw [abs_le] at this
      have := le_abs_self (a z₀); linarith
  · rw [abs_of_neg hneg] at hcon
    refine key (a z₀ - K - 1) (Or.inr ⟨fun w hw => ?_, fun w hw => ?_⟩)
    · have := hout w hw; rw [abs_le] at this; linarith
    · have := hin w hw; rw [abs_le] at this
      have := neg_abs_le (a z₀); linarith

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u)
    (hG : ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ z : ℂ, z ≠ 0 → ‖z‖ < r → ‖z‖ * gradNorm H u z ≤ C)
    (hQ : Tendsto (fun ρ => loopAction H u (cwLoop 0 ρ)) (𝓝[>] 0) (𝓝 0)) :
    ∃ r : ℝ, 0 < r ∧ ∃ A : ℝ, ∀ z : ℂ, z ≠ 0 → ‖z‖ < r → |aCoord H (u z)| ≤ A :=
  FiniteEnergyPlane.exists_abs_aCoord_le_of_tendsto_loopAction_zero_aux H hH J hJ u hu hG hQ
