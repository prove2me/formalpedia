-- Prove2me | solution 1 for FriedCrossing.PureZeros.abs_le_of_vanish_axes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:57:26.079479+00:00
-- url     : https://prove2.me/submissions/a1e990fc-4edd-4c77-b033-217fcf5c21f0

import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Theorems.Thm_FriedCrossing_Hadamard_entry_slope_eq


set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.PureZeros
open TwinRate
namespace FriedCrossing.PureZeros
theorem _root_.solution {f fτ fθτ : ℝ → ℝ → ℝ} {K ε : ℝ} (hε : 0 < ε)
    (h0τ : ∀ θ, f θ 0 = 0) (h0θ : ∀ τ, f 0 τ = 0)
    (hτ : ∀ θ τ, HasDerivAt (f θ) (fτ θ τ) τ)
    (hθ : ∀ θ τ, HasDerivAt (fun θ => fτ θ τ) (fθτ θ τ) θ)
    (hK : ∀ θ τ, |θ| < ε → |τ| < ε → |fθτ θ τ| ≤ K)
    {θ τ : ℝ} (hθε : |θ| < ε) (hτε : |τ| < ε) : |f θ τ| ≤ K * |θ| * |τ| := by
  have hK0 : 0 ≤ K :=
    le_trans (abs_nonneg _) (hK 0 0 (by simpa using hε) (by simpa using hε))
  have hfτ0 : ∀ ξ, fτ 0 ξ = 0 := fun ξ => by
    have h1 : HasDerivAt (f 0) (fτ 0 ξ) ξ := hτ 0 ξ
    have h2 : HasDerivAt (f 0) 0 ξ := by
      have : f 0 = fun _ => (0 : ℝ) := funext h0θ
      rw [this]; exact hasDerivAt_const ξ (0 : ℝ)
    exact h1.unique h2
  by_cases hτ0 : τ = 0
  · subst hτ0; rw [h0τ, abs_zero]; positivity
  obtain ⟨ξ, hξ, hslope⟩ := Hadamard.entry_slope_eq (hτ θ) hτ0
  rw [h0τ, sub_zero] at hslope
  have hfval : f θ τ = τ * fτ θ ξ := by rw [← hslope]; field_simp
  by_cases hθ0 : θ = 0
  · subst hθ0; rw [hfval, hfτ0, mul_zero, abs_zero]; positivity
  obtain ⟨η, hη, hslope2⟩ := Hadamard.entry_slope_eq (fun t => hθ t ξ) hθ0
  rw [hfτ0, sub_zero] at hslope2
  have hfτval : fτ θ ξ = θ * fθτ η ξ := by rw [← hslope2]; field_simp
  rw [hfval, hfτval, abs_mul, abs_mul]
  have hb := hK η ξ (lt_trans hη hθε) (lt_trans hξ hτε)
  calc |τ| * (|θ| * |fθτ η ξ|) ≤ |τ| * (|θ| * K) := by gcongr
    _ = K * |θ| * |τ| := by ring
end FriedCrossing.PureZeros
