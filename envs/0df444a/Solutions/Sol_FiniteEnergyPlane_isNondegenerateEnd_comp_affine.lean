-- Prove2me | solution 1 for FiniteEnergyPlane.isNondegenerateEnd_comp_affine
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-03T09:23:36.436191+00:00
-- url     : https://prove2.me/submissions/ea04a844-4342-4b45-aadb-df3173663b7f

import Definitions.Def_FiniteEnergyPlane_Winding
import Mathlib



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

lemma c3c_cylEnd (z₀ : ℂ) (r : ℝ) (hr : 0 < r) (s t : ℝ) :
    z₀ + (r : ℂ) * cylEnd s t = cylEndAt z₀ (s + -Real.log r / (2 * π)) t := by
  unfold cylEnd cylEndAt cwLoop
  have hexp : Real.exp (-(2 * π * (s + -Real.log r / (2 * π)))) = r * Real.exp (-(2 * π * s)) := by
    have hπ : (2 * π) ≠ 0 := by positivity
    rw [show -(2 * π * (s + -Real.log r / (2 * π))) = Real.log r + -(2 * π * s) by
      field_simp; ring, Real.exp_add, Real.exp_log hr]
  rw [hexp]
  push_cast
  ring

theorem isNondegenerateEnd_comp_affine_aux {n : ℕ} (H : V n → ℝ) (u : ℂ → V n) (z₀ : ℂ) (r : ℝ)
    (hr : 0 < r) (P : ReebOrbit H) (ε : ℝ) (hnd : IsNondegenerateEnd H u (cylEndAt z₀) P ε) :
    IsNondegenerateEnd H (fun z => u (z₀ + (r : ℂ) * z)) cylEnd P ε := by
  obtain ⟨d, c, b, hb, hA, hW⟩ := hnd
  set σ : ℝ := -Real.log r / (2 * π) with hσ
  have hA' : ∀ p : ℝ × ℝ, endA H (fun z => u (z₀ + (r : ℂ) * z)) cylEnd p =
      endA H u (cylEndAt z₀) (p.1 + σ, p.2) := fun p => by
    show aCoord H (u (z₀ + (r : ℂ) * cylEnd p.1 p.2)) = aCoord H (u (cylEndAt z₀ (p.1 + σ) p.2))
    rw [c3c_cylEnd z₀ r hr]
  have hW' : ∀ p : ℝ × ℝ, endW H (fun z => u (z₀ + (r : ℂ) * z)) cylEnd p =
      endW H u (cylEndAt z₀) (p.1 + σ, p.2) := fun p => by
    show proj H (u (z₀ + (r : ℂ) * cylEnd p.1 p.2)) = proj H (u (cylEndAt z₀ (p.1 + σ) p.2))
    rw [c3c_cylEnd z₀ r hr]
  refine ⟨d + ε * P.T * σ, c, b, hb, ?_, ?_⟩
  · intro η hη
    obtain ⟨s₀, hs₀⟩ := hA η hη
    refine ⟨s₀ - σ, fun s hs t => ?_⟩
    have := hs₀ (s + σ) (by linarith) t
    dsimp only at this ⊢
    rw [hA']
    convert this using 2
    ring
  · intro η hη
    obtain ⟨s₀, hs₀⟩ := hW (η * Real.exp (b * σ)) (by positivity)
    refine ⟨s₀ - σ, fun s hs t => ?_⟩
    have := hs₀ (s + σ) (by linarith) t
    simp only at this ⊢
    rw [hW']
    have hsplit : Real.exp (b * s) • (endW H u (cylEndAt z₀) (s + σ, t) - P.x (ε * P.T * t + c)) =
        Real.exp (-(b * σ)) • (Real.exp (b * (s + σ)) •
          (endW H u (cylEndAt z₀) (s + σ, t) - P.x (ε * P.T * t + c))) := by
      rw [smul_smul, ← Real.exp_add]; congr 2; ring
    rw [hsplit, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    calc Real.exp (-(b * σ)) * ‖_‖ ≤ Real.exp (-(b * σ)) * (η * Real.exp (b * σ)) :=
          mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
      _ = η := by
          rw [mul_comm η, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ) (u : ℂ → V n) (z₀ : ℂ) (r : ℝ)
    (hr : 0 < r) (P : ReebOrbit H) (ε : ℝ) (hnd : IsNondegenerateEnd H u (cylEndAt z₀) P ε) :
    IsNondegenerateEnd H (fun z => u (z₀ + (r : ℂ) * z)) cylEnd P ε :=
  isNondegenerateEnd_comp_affine_aux H u z₀ r hr P ε hnd
