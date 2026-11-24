-- Prove2me | solution 1 for FiniteEnergyPlane.isNondegenerateEnd_comp_exp_mul
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-23T22:27:10.676829+00:00
-- url     : https://prove2.me/submissions/c1272bd0-0535-4209-8ab5-d5f83da1b8a3

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Mathlib



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem isNondegenerateEnd_comp_exp_mul_aux {n : ℕ} (H : V n → ℝ) (u : ℂ → V n) (P : ReebOrbit H)
    (huP : IsNondegenerateEnd H u cylInf P 1) (α : ℝ) :
    IsNondegenerateEnd H (fun z => u (Complex.exp (((2 * π * α : ℝ) : ℂ) * Complex.I) * z))
      cylInf P 1 := by
  obtain ⟨d, c, b, hb, h1, h2⟩ := huP
  have hcyl : ∀ s t : ℝ, Complex.exp (((2 * π * α : ℝ) : ℂ) * Complex.I) * cylInf s t =
      cylInf s (t + α) := by
    intro s t
    unfold cylInf ccwLoop
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  refine ⟨d, c + P.T * α, b, hb, fun ε hε => ?_, fun ε hε => ?_⟩
  · obtain ⟨s₀, hs⟩ := h1 ε hε
    refine ⟨s₀, fun s hs' t => ?_⟩
    have := hs s hs' (t + α)
    simpa only [endA, hcyl] using this
  · obtain ⟨s₀, hs⟩ := h2 ε hε
    refine ⟨s₀, fun s hs' t => ?_⟩
    have := hs s hs' (t + α)
    simp only [endW, hcyl] at this ⊢
    rwa [show 1 * P.T * t + (c + P.T * α) = 1 * P.T * (t + α) + c by ring]

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ) (u : ℂ → V n) (P : ReebOrbit H)
    (huP : IsNondegenerateEnd H u cylInf P 1) (α : ℝ) :
    IsNondegenerateEnd H (fun z => u (Complex.exp (((2 * π * α : ℝ) : ℂ) * Complex.I) * z))
      cylInf P 1 :=
  isNondegenerateEnd_comp_exp_mul_aux H u P huP α
