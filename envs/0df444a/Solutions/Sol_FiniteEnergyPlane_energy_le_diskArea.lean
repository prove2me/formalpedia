-- Prove2me | solution 1 for FiniteEnergyPlane.energy_le_diskArea
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-26T19:50:34.408463+00:00
-- url     : https://prove2.me/submissions/e80213c9-93ba-4bd8-ab6f-7b937c38e06a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_FiniteEnergyPlane_SpanningDisk
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_energy_le_loopAction_of_aCoord_eq_zero
import Theorems.Thm_FiniteEnergyPlane_ofReal_loopAction_le_diskArea

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal Real

namespace FiniteEnergyPlane

theorem eld_aCoord_of_mem {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (x : V n) (hx : H x = 1) : aCoord H x = 0 := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    have := hH.2.2 0 hx
    simp at this
  obtain ⟨r, ⟨hr0, hr1⟩, hru⟩ := hH.2.1 x hx0
  have e1 : ∃ r : ℝ, 0 < r ∧ H (r • x) = 1 := ⟨r, hr0, hr1⟩
  have h1 : scaleToS H x = 1 := by
    unfold scaleToS
    rw [dif_pos e1]
    have := hru _ (Classical.choose_spec e1)
    have h1' := hru 1 ⟨one_pos, by rw [one_smul]; exact hx⟩
    rw [this, h1']
  unfold aCoord; rw [h1, Real.log_one]; simp

theorem eld_exists_ccwLoop {ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) 1) : ∃ t : ℝ, ccwLoop 1 t = ζ := by
  refine ⟨Complex.arg ζ / (2 * π), ?_⟩
  have hn : ‖ζ‖ = 1 := by simpa using hζ
  unfold ccwLoop
  have : ((2 * π * (Complex.arg ζ / (2 * π)) : ℝ) : ℂ) = (Complex.arg ζ : ℂ) := by
    congr 1; field_simp
  rw [this]
  have := Complex.norm_mul_exp_arg_mul_I ζ
  rw [hn] at this
  push_cast at this ⊢
  simpa using this

theorem energy_le_diskArea_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (e : ℂ → V 1) (z₀ : ℂ) (he : IsSpecialSpanningDisk H P e z₀)
    (Γ : Finset ℂ) (u : ℂ → V 1) (hu : IsDiskCurve H J e z₀ (closedBall 0 1) Γ u)
    (hΓ : ∀ z ∈ Γ, Tendsto (fun w => aCoord H (u w)) (𝓝[≠] z) atBot) :
    energy H (ball 0 1 \ Γ) u ≤ diskArea e := by
  obtain ⟨hΓ₁, hsm, hu0, hhol, -, c, hc, -⟩ := id hu
  obtain ⟨⟨ρ, ⟨-, hρ, hmaps, -, -⟩, -⟩, -⟩ := id he
  have hbd : ∀ z ∈ sphere (0 : ℂ) 1, aCoord H (u z) = 0 := by
    intro z hz
    obtain ⟨t, rfl⟩ := eld_exists_ccwLoop hz
    obtain ⟨hct, hut⟩ := hc t
    rw [hut]
    have hcρ : c t ∈ ball (0 : ℂ) ρ :=
      mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hct) hρ)
    exact eld_aCoord_of_mem H hH _ (hmaps hcρ)
  exact (energy_le_loopAction_of_aCoord_eq_zero H hH J hJ Γ hΓ₁ u hsm hu0 hhol hbd hΓ).trans
    (ofReal_loopAction_le_diskArea H hH J hJ P e z₀ he Γ u hu hΓ)

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (e : ℂ → V 1) (z₀ : ℂ) (he : IsSpecialSpanningDisk H P e z₀)
    (Γ : Finset ℂ) (u : ℂ → V 1) (hu : IsDiskCurve H J e z₀ (closedBall 0 1) Γ u)
    (hΓ : ∀ z ∈ Γ, Tendsto (fun w => aCoord H (u w)) (𝓝[≠] z) atBot) :
    energy H (ball 0 1 \ Γ) u ≤ diskArea e :=
  energy_le_diskArea_aux H hH J hJ P e z₀ he Γ u hu hΓ
