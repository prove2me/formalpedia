-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.spherical_sensitive_dependence_paper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:16:19.823059+00:00
-- url     : https://prove2.me/submissions/d4e81ee2-2ea4-4e8b-883b-431ac082f249

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Interval.Set.Infinite
import Definitions.Def_ExpChaotic_Dynamics
import Definitions.Def_ExpChaotic_PaperConsequences
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_eventually_hits_nonzero
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_succ
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_zero
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_succ
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_zero



set_option autoImplicit true
open Function Filter Set Metric
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution {U : Set ℂ}
    (hU : IsOpen U) (hUne : U.Nonempty) {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ z ∈ U, ∃ w ∈ U,
      ‖expIterate n z‖ ≤ R ∧ δ ≤ ‖expIterate n z - expIterate n w‖ := by
  let a : ℂ := (R / 2 : ℝ)
  let b : ℂ := (R / 2 + δ : ℝ)
  have ha : a ≠ 0 := by dsimp [a]; exact_mod_cast (ne_of_gt (half_pos hR))
  have hb : b ≠ 0 := by dsimp [b]; exact_mod_cast (ne_of_gt (by positivity : 0 < R / 2 + δ))
  obtain ⟨N₁, h₁⟩ := eventually_hits_nonzero hU hUne ha
  obtain ⟨N₂, h₂⟩ := eventually_hits_nonzero hU hUne hb
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  obtain ⟨z, hz, hza⟩ := h₁ n ((le_max_left _ _).trans hn)
  obtain ⟨w, hw, hwb⟩ := h₂ n ((le_max_right _ _).trans hn)
  refine ⟨z, hz, w, hw, ?_, ?_⟩
  · rw [hza]
    simpa [a, Complex.norm_real, abs_of_pos hR] using (half_le_self hR.le)
  · rw [hza, hwb]
    have hab : a - b = (-δ : ℝ) := by dsimp [a, b]; push_cast; ring
    simp [hab, Complex.norm_real, abs_of_pos hδ]
end ExponentialJuliaSetMisiurewicz
