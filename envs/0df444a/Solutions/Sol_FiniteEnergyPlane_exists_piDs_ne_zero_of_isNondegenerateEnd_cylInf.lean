-- Prove2me | solution 1 for FiniteEnergyPlane.exists_piDs_ne_zero_of_isNondegenerateEnd_cylInf
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-03T09:42:10.990367+00:00
-- url     : https://prove2.me/submissions/a010c68a-6e22-4190-865b-2300d85cc355

import Definitions.Def_FiniteEnergyPlane_Winding
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_piDs_ne_zero_iff_dlambdaDensity_pos
import Theorems.Thm_FiniteEnergyPlane_isFiniteEnergyCurve_comp_inv_exterior
import Theorems.Thm_FiniteEnergyPlane_exists_ball_piDs_ne_zero_of_isNondegenerateEnd



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

lemma c4_inv_cylEndAt (s t : ℝ) : (cylEndAt 0 s t)⁻¹ = cylInf s t := by
  unfold cylEndAt cylInf cwLoop ccwLoop
  rw [zero_add, mul_inv, ← Complex.exp_neg, ← Complex.ofReal_inv, ← Real.exp_neg, neg_neg,
    neg_mul, neg_neg]

lemma c4_inv_mem {a : ℝ} (ha : 0 < a) {w : ℂ} (hw : 1 / a < ‖w‖) :
    w⁻¹ ∈ ball (0 : ℂ) a \ {0} := by
  have hw0 : 0 < ‖w‖ := lt_trans (by positivity) hw
  refine ⟨?_, ?_⟩
  · rw [mem_ball_zero_iff, norm_inv]
    exact (inv_lt_comm₀ hw0 ha).2 (by simpa [one_div] using hw)
  · simpa using norm_pos_iff.1 hw0

lemma c4_lt_of_mem {a : ℝ} {z : ℂ} (hz : z ∈ ball (0 : ℂ) a \ {0}) : 1 / a < ‖z⁻¹‖ := by
  obtain ⟨hzb, hz0⟩ := hz
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hlt : ‖z‖ < a := mem_ball_zero_iff.1 hzb
  rw [norm_inv, one_div]
  exact (inv_lt_inv₀ (lt_trans hn hlt) hn).2 hlt

theorem exists_piDs_ne_zero_of_isNondegenerateEnd_cylInf_aux (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (R : ℝ) (u : ℂ → V 1) (hu : IsFiniteEnergyCurve H J {z | R < ‖z‖} u) (P : ReebOrbit H)
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (hnd : IsNondegenerateEnd H u cylInf P ε)
    (hfreq : ∀ R' : ℝ, ∃ z : ℂ, R' < ‖z‖ ∧ piDs H u z ≠ 0) :
    ∃ R' : ℝ, ∀ z : ℂ, R' < ‖z‖ → piDs H u z ≠ 0 := by
  have hm : 0 < max R 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  set ρ : ℝ := 1 / max R 1 with hρdef
  have hρ : 0 < ρ := by positivity
  have hRρ : R * ρ ≤ 1 := by
    rw [hρdef, mul_one_div, div_le_one hm]; exact le_max_left _ _
  set v : ℂ → V 1 := fun z => u z⁻¹ with hvdef
  obtain ⟨hv, hden⟩ := isFiniteEnergyCurve_comp_inv_exterior H hH J hJ R ρ hρ hRρ u hu
  have hUo : IsOpen {z : ℂ | R < ‖z‖} := isOpen_lt continuous_const continuous_norm
  have hBo : IsOpen (ball (0 : ℂ) ρ \ {0}) := isOpen_ball.sdiff isClosed_singleton
  -- `R < ‖z⁻¹‖` on the punctured disc
  have hRin : ∀ z ∈ ball (0 : ℂ) ρ \ {0}, R < ‖z⁻¹‖ := by
    intro z hz
    have h1 := c4_lt_of_mem hz
    have h2 : R ≤ 1 / ρ := by rw [hρdef, one_div_one_div]; exact le_max_left _ _
    linarith
  have hequiv : ∀ z ∈ ball (0 : ℂ) ρ \ {0}, piDs H v z ≠ 0 ↔ piDs H u z⁻¹ ≠ 0 := by
    intro z hz
    have hz0 : z ≠ 0 := hz.2
    rw [piDs_ne_zero_iff_dlambdaDensity_pos H hH J hJ _ hBo v hv.2.1 hv.2.2.1 hz,
      piDs_ne_zero_iff_dlambdaDensity_pos H hH J hJ _ hUo u hu.2.1 hu.2.2.1 (hRin z hz),
      hden z hz0 (hRin z hz)]
    have hp : 0 < (‖z‖ ^ 4)⁻¹ := by
      have := norm_pos_iff.2 hz0; positivity
    exact mul_pos_iff_of_pos_left hp
  have hnd' : IsNondegenerateEnd H v (cylEndAt 0) P ε := by
    unfold IsNondegenerateEnd endA endW at hnd ⊢
    simpa only [hvdef, c4_inv_cylEndAt] using hnd
  have hfreq' : ∀ ρ' > (0 : ℝ), ∃ z ∈ ball (0 : ℂ) ρ' \ {0}, piDs H v z ≠ 0 := by
    intro ρ' hρ'
    obtain ⟨w, hw, hne⟩ := hfreq (max (1 / ρ') (1 / ρ))
    have hw1 : w⁻¹ ∈ ball (0 : ℂ) ρ \ {0} := c4_inv_mem hρ (lt_of_le_of_lt (le_max_right _ _) hw)
    refine ⟨w⁻¹, c4_inv_mem hρ' (lt_of_le_of_lt (le_max_left _ _) hw), ?_⟩
    rw [hequiv _ hw1, inv_inv]; exact hne
  obtain ⟨ρ₀, hρ₀, hpos⟩ := exists_ball_piDs_ne_zero_of_isNondegenerateEnd H hH J hJ 0 ρ hρ v hv
    P ε hε hnd' hfreq'
  refine ⟨max (1 / ρ₀) (1 / ρ), fun z hz => ?_⟩
  have hz1 : z⁻¹ ∈ ball (0 : ℂ) ρ \ {0} := c4_inv_mem hρ (lt_of_le_of_lt (le_max_right _ _) hz)
  have h := hpos _ (c4_inv_mem hρ₀ (lt_of_le_of_lt (le_max_left _ _) hz))
  rw [hequiv _ hz1, inv_inv] at h
  exact h

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (R : ℝ) (u : ℂ → V 1) (hu : IsFiniteEnergyCurve H J {z | R < ‖z‖} u) (P : ReebOrbit H)
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (hnd : IsNondegenerateEnd H u cylInf P ε)
    (hfreq : ∀ R' : ℝ, ∃ z : ℂ, R' < ‖z‖ ∧ piDs H u z ≠ 0) :
    ∃ R' : ℝ, ∀ z : ℂ, R' < ‖z‖ → piDs H u z ≠ 0 :=
  exists_piDs_ne_zero_of_isNondegenerateEnd_cylInf_aux H hH J hJ R u hu P ε hε hnd hfreq
