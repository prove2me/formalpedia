-- Prove2me | solution 1 for FriedCrossing.PureZeros.crossing_estimates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:00:25.391901+00:00
-- url     : https://prove2.me/submissions/1082a2d1-8685-4a57-a129-6773197445b5

import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Theorems.Thm_FriedCrossing_PureZeros_abs_le_of_vanish_axes
import Theorems.Thm_P2M_FriedCrossing_PureZeros_abs_le_of_vanish___defcde5ba42b
import Theorems.Thm_FriedCrossing_PureZeros_deriv_zero_of_zero_fun

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.PureZeros
open TwinRate
namespace FriedCrossing.PureZeros
theorem _root_.solution
    (sStar : ℝ → ℝ) (e₁ e₂ e₁τ e₁θτ e₂τ e₂ττ e₂θττ : ℝ → ℝ → ℝ) {r₀ K₁ K₂ ε : ℝ}
    (hr₀ : 0 < r₀) (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) (hε : 0 < ε)
    (hd₁ : ∀ θ τ, HasDerivAt (e₁ θ) (e₁τ θ τ) τ)
    (hd₁' : ∀ θ τ, HasDerivAt (fun θ => e₁τ θ τ) (e₁θτ θ τ) θ)
    (hB₁ : ∀ θ τ, |θ| < ε → |τ| < ε → |e₁θτ θ τ| ≤ K₁)
    (hd₂ : ∀ θ τ, HasDerivAt (e₂ θ) (e₂τ θ τ) τ)
    (hd₂' : ∀ θ τ, HasDerivAt (e₂τ θ) (e₂ττ θ τ) τ)
    (hd₂'' : ∀ θ τ, HasDerivAt (fun θ => e₂ττ θ τ) (e₂θττ θ τ) θ)
    (hB₂ : ∀ θ τ, |θ| < ε → |τ| < ε → |e₂θττ θ τ| ≤ K₂)
    (h₁τ0 : ∀ θ, e₁ θ 0 = 0) (h₁θ0 : ∀ τ, e₁ 0 τ = 0)
    (h₂τ0 : ∀ θ, e₂ θ 0 = -(sStar θ) ^ 2) (h₂θ0 : ∀ τ, e₂ 0 τ = 0)
    {θ σ : ℝ} (hθε : |θ| < ε) (hθ1 : |θ| < r₀ ^ 2 / (8 * K₂)) (hθ2 : |θ| < r₀ / (16 * K₁))
    (hs : sStar θ < 0) (hσpos : 0 < σ) (hσle : σ ≤ 2 * |sStar θ| / r₀) (hσε : σ < ε)
    (h₂σ : e₂ θ σ = 0) :
    |e₁ θ σ| ≤ K₁ * |θ| * σ ∧ r₀ * |sStar θ| / 4 ≤ |e₂τ θ σ| ∧
      (e₁ θ σ ≠ 0 → 2 * r₀ < |e₂τ θ σ / e₁ θ σ|) := by
  set S := |sStar θ| with hS
  have hSpos : 0 < S := abs_pos.mpr hs.ne
  have hσabs : |σ| < ε := by rw [abs_of_pos hσpos]; exact hσε
  -- (i)
  have hi : |e₁ θ σ| ≤ K₁ * |θ| * σ := by
    have := abs_le_of_vanish_axes hε h₁τ0 h₁θ0 hd₁ hd₁' hB₁ hθε hσabs
    rwa [abs_of_pos hσpos] at this
  -- ∂²_τ e₂ vanishes on θ = 0, hence is O(|θ|)
  have hττ0 : ∀ τ, e₂ττ 0 τ = 0 := by
    have hτ0 : ∀ τ, e₂τ 0 τ = 0 := deriv_zero_of_zero_fun h₂θ0 (hd₂ 0)
    exact deriv_zero_of_zero_fun hτ0 (hd₂' 0)
  have hττ_small : ∀ τ, |τ| < ε → |e₂ττ θ τ| ≤ K₂ * |θ| := fun τ hτ =>
    abs_le_of_vanish_θ hε hττ0 hd₂'' hB₂ hθε hτ
  -- mean value on [0, σ]: ∂_τe₂(θ,ξ) = s*²/σ
  have hcont₂ : ContinuousOn (e₂ θ) (Set.Icc 0 σ) := fun τ _ =>
    (hd₂ θ τ).continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ, hξslope⟩ := exists_hasDerivAt_eq_slope (e₂ θ) (e₂τ θ) hσpos hcont₂
    (fun τ _ => hd₂ θ τ)
  rw [h₂σ, h₂τ0, sub_zero, zero_sub, neg_neg] at hξslope
  -- ∂_τe₂(θ,ξ) = S²/σ
  have hξval : e₂τ θ ξ = S ^ 2 / σ := by rw [hξslope, hS, sq_abs]
  -- mean value on [ξ, σ] for ∂_τe₂
  have hcont₂' : ContinuousOn (e₂τ θ) (Set.Icc ξ σ) := fun τ _ =>
    (hd₂' θ τ).continuousAt.continuousWithinAt
  obtain ⟨η, hη, hηslope⟩ := exists_hasDerivAt_eq_slope (e₂τ θ) (e₂ττ θ) hξ.2 hcont₂'
    (fun τ _ => hd₂' θ τ)
  have hηabs : |η| < ε := by
    rw [abs_of_pos (lt_trans hξ.1 hη.1)]; exact lt_trans hη.2 hσε
  have hdiff : |e₂τ θ σ - e₂τ θ ξ| ≤ K₂ * |θ| * σ := by
    have h1 : e₂τ θ σ - e₂τ θ ξ = e₂ττ θ η * (σ - ξ) := by
      rw [hηslope]; exact (div_mul_cancel₀ _ (sub_pos.mpr hξ.2).ne').symm
    rw [h1, abs_mul, abs_of_pos (sub_pos.mpr hξ.2)]
    calc |e₂ττ θ η| * (σ - ξ) ≤ (K₂ * |θ|) * σ :=
          mul_le_mul (hττ_small η hηabs) (by linarith [hξ.1]) (by linarith [hξ.2])
            (by positivity)
      _ = K₂ * |θ| * σ := by ring
  -- numeric bounds
  have hσinv : S * r₀ / 2 ≤ S ^ 2 / σ := by
    have h2S : 0 < 2 * S / r₀ := by positivity
    calc S * r₀ / 2 = S ^ 2 / (2 * S / r₀) := by field_simp
      _ ≤ S ^ 2 / σ := div_le_div_of_nonneg_left (sq_nonneg S) hσpos hσle
  have hK₂σ : K₂ * |θ| * σ ≤ r₀ * S / 4 := by
    have hθ1' : |θ| * (8 * K₂) < r₀ ^ 2 := (lt_div_iff₀ (by positivity)).mp hθ1
    calc K₂ * |θ| * σ ≤ K₂ * |θ| * (2 * S / r₀) := by gcongr
      _ = (|θ| * (8 * K₂)) * (S / (4 * r₀)) := by field_simp; ring
      _ ≤ r₀ ^ 2 * (S / (4 * r₀)) := by gcongr
      _ = r₀ * S / 4 := by field_simp
  have hii : r₀ * S / 4 ≤ |e₂τ θ σ| := by
    have h1 : |e₂τ θ ξ| - |e₂τ θ σ - e₂τ θ ξ| ≤ |e₂τ θ σ| := by
      have := abs_sub_abs_le_abs_sub (e₂τ θ ξ) (e₂τ θ σ)
      rw [abs_sub_comm] at this
      linarith
    have h2 : |e₂τ θ ξ| = S ^ 2 / σ := by
      rw [hξval, abs_of_pos (by positivity)]
    linarith
  refine ⟨hi, hii, fun he1 => ?_⟩
  -- (iii)
  have he1pos : 0 < |e₁ θ σ| := abs_pos.mpr he1
  have hU : |e₁ θ σ| ≤ 2 * K₁ * |θ| * S / r₀ := by
    calc |e₁ θ σ| ≤ K₁ * |θ| * σ := hi
      _ ≤ K₁ * |θ| * (2 * S / r₀) := by gcongr
      _ = 2 * K₁ * |θ| * S / r₀ := by ring
  have hθ2' : |θ| * (16 * K₁) < r₀ := (lt_div_iff₀ (by positivity)).mp hθ2
  have hkey : 2 * r₀ * |e₁ θ σ| < |e₂τ θ σ| := by
    calc 2 * r₀ * |e₁ θ σ| ≤ 2 * r₀ * (2 * K₁ * |θ| * S / r₀) := by gcongr
      _ = (|θ| * (16 * K₁)) * (S / 4) := by field_simp; ring
      _ < r₀ * (S / 4) := by gcongr
      _ = r₀ * S / 4 := by ring
      _ ≤ |e₂τ θ σ| := hii
  rw [abs_div]
  exact (lt_div_iff₀ he1pos).mpr hkey
end FriedCrossing.PureZeros
