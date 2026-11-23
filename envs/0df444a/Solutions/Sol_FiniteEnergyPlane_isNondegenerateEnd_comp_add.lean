-- Prove2me | solution 1 for FiniteEnergyPlane.isNondegenerateEnd_comp_add
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-23T21:16:24.900563+00:00
-- url     : https://prove2.me/submissions/92c3d83d-1e15-47f5-aa38-71553e964b5a

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Mathlib
import Definitions.Def_FiniteEnergyPlane_Fredholm
import Theorems.Thm_FiniteEnergyPlane_contDiffAt_aCoord_proj
import Theorems.Thm_FiniteEnergyPlane_exists_norm_mul_gradNorm_le_of_plane
import Theorems.Thm_FiniteEnergyPlane_isNondegenerateEnd_of_aCoord_proj_sub_le
import Theorems.Thm_FiniteEnergyPlane_isNondegenerateEnd_of_comp_eq_shift
import Theorems.Thm_FiniteEnergyPlane_rescale_isFiniteEnergyCurve
import Theorems.Thm_FiniteEnergyPlane_isPrime_of_isFastPlane_of_isNondegenerateEnd
import Theorems.Thm_FiniteEnergyPlane_piDs_ne_zero_of_isFastPlane
import Theorems.Thm_FiniteEnergyPlane_piDs_ne_zero_iff_dlambdaDensity_pos



/-! Real affine changes of the domain of an embedded fast plane. -/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Translation of the domain keeps a nondegenerate end at `∞`. -/
theorem isNondegenerateEnd_comp_add_aux {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J Set.univ u) (P : ReebOrbit H)
    (huP : IsNondegenerateEnd H u cylInf P 1) (b : ℂ) :
    IsNondegenerateEnd H (fun z => u (z + b)) cylInf P 1 := by
  obtain ⟨C, hC⟩ := exists_norm_mul_gradNorm_le_of_plane H hH J hJ u hu
  have hs : ContDiff ℝ ∞ u := contDiffOn_univ.1 hu.1
  have ha : Differentiable ℝ (fun z => aCoord H (u z)) := fun z =>
    ((contDiffAt_aCoord_proj H hH (u z) (hu.2.1 z trivial)).1.comp z hs.contDiffAt).differentiableAt
      (by simp)
  have hp : Differentiable ℝ (fun z => proj H (u z)) := fun z =>
    ((contDiffAt_aCoord_proj H hH (u z) (hu.2.1 z trivial)).2.comp z hs.contDiffAt).differentiableAt
      (by simp)
  have hC0 : 0 ≤ C := le_trans (by unfold gradNorm; positivity) (hC 0)
  refine isNondegenerateEnd_of_aCoord_proj_sub_le H P u _ huP (2 * ‖b‖ + 1) (4 * C * ‖b‖) 1
    one_pos fun z hz => ?_
  have hb0 := norm_nonneg b
  have hz0 : 0 < ‖z‖ := by linarith
  have hgrad : ∀ x ∈ segment ℝ z (z + b), gradNorm H u x ≤ 2 * C / ‖z‖ := by
    intro x hx
    have hxz : ‖x - z‖ ≤ ‖b‖ := by
      have := norm_sub_le_of_mem_segment hx
      simpa using this
    have h1 : ‖z‖ / 2 ≤ ‖x‖ := by
      have := norm_sub_norm_le z (z - x)
      rw [sub_sub_cancel, norm_sub_rev] at this
      linarith
    rw [le_div_iff₀ hz0]
    have h0 : 0 ≤ gradNorm H u x := by unfold gradNorm; positivity
    nlinarith [hC x]
  have hfin : 2 * C / ‖z‖ * ‖b‖ ≤ 4 * C * ‖b‖ * (1 + ‖z‖) ^ (-(1 : ℝ)) := by
    rw [Real.rpow_neg_one, ← div_eq_mul_inv, div_mul_eq_mul_div, div_le_div_iff₀ hz0 (by linarith)]
    nlinarith [mul_nonneg hC0 hb0]
  have key : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (g : ℂ → F),
      Differentiable ℝ g → (∀ x, ‖fderiv ℝ g x‖ ≤ gradNorm H u x) →
      ‖g (z + b) - g z‖ ≤ 4 * C * ‖b‖ * (1 + ‖z‖) ^ (-(1 : ℝ)) := by
    intro F _ _ g hg hgn
    have := (convex_segment z (z + b)).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
      (fun x _ => hg x) (fun x hx => (hgn x).trans (hgrad x hx)) (left_mem_segment ℝ z (z + b))
      (right_mem_segment ℝ z (z + b))
    rw [add_sub_cancel_left] at this
    exact this.trans hfin
  refine ⟨?_, ?_⟩
  · have := key (fun z => aCoord H (u z)) ha fun x => by
      unfold gradNorm; linarith [norm_nonneg (fderiv ℝ (fun z => proj H (u z)) x)]
    rwa [Real.norm_eq_abs] at this
  · exact key (fun z => proj H (u z)) hp fun x => by
      unfold gradNorm; linarith [norm_nonneg (fderiv ℝ (fun z => aCoord H (u z)) x)]

/-- Positive rescaling of the domain keeps a nondegenerate end at `∞`. -/
theorem isNondegenerateEnd_comp_smul_aux {n : ℕ} (H : V n → ℝ) (u : ℂ → V n) (P : ReebOrbit H)
    (huP : IsNondegenerateEnd H u cylInf P 1) (ρ : ℝ) (hρ : 0 < ρ) :
    IsNondegenerateEnd H (fun z => u (ρ • z)) cylInf P 1 := by
  refine isNondegenerateEnd_of_comp_eq_shift H _ u cylInf cylInf (-Real.log ρ / (2 * π))
    (fun s t => ?_) P 1 huP
  show u _ = u _
  congr 1
  unfold cylInf ccwLoop
  have : Real.exp (2 * π * (s + -Real.log ρ / (2 * π))) = Real.exp (2 * π * s) / ρ := by
    have hπ : (2 * π) ≠ 0 := by positivity
    rw [show 2 * π * (s + -Real.log ρ / (2 * π)) = 2 * π * s - Real.log ρ by field_simp; ring,
      Real.exp_sub, Real.exp_log hρ]
  rw [this, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, mul_div_cancel₀ _ hρ.ne']

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J Set.univ u) (P : ReebOrbit H)
    (huP : IsNondegenerateEnd H u cylInf P 1) (b : ℂ) :
    IsNondegenerateEnd H (fun z => u (z + b)) cylInf P 1 :=
  isNondegenerateEnd_comp_add_aux H hH J hJ u hu P huP b
