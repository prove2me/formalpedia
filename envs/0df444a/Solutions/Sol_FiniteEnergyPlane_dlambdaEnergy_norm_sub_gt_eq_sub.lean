-- Prove2me | solution 1 for FiniteEnergyPlane.dlambdaEnergy_norm_sub_gt_eq_sub
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-22T19:46:57.312881+00:00
-- url     : https://prove2.me/submissions/16992819-7a02-4717-af04-6a8b94d3513c

import Definitions.Def_FiniteEnergyPlane_Setting
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_dlambdaEnergy_ne_top_of_univ_eq_ofReal



/-! dλ-energy bookkeeping on discs. -/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem dlambdaEnergy_norm_sub_gt_eq_sub_aux {n : ℕ} (H : V n → ℝ) (u : ℂ → V n) (T : ℝ)
    (htot : dlambdaEnergy H Set.univ u = ENNReal.ofReal T) (ζ : ℂ) (ρ : ℝ) :
    dlambdaEnergy H {x | ρ < ‖x - ζ‖} u = ENNReal.ofReal T - dlambdaEnergy H (ball ζ ρ) u := by
  have hfin := dlambdaEnergy_ne_top_of_univ_eq_ofReal H u T htot (ball ζ ρ)
  unfold dlambdaEnergy at htot hfin ⊢
  have h1 := lintegral_add_compl (μ := volume) (fun z => ENNReal.ofReal (dlambdaDensity H u z))
    (measurableSet_ball (x := ζ) (ε := ρ))
  have hcompl : (ball ζ ρ)ᶜ = {x | ρ < ‖x - ζ‖} ∪ sphere ζ ρ := by
    ext x
    simp only [Set.mem_compl_iff, Metric.mem_ball, Set.mem_union, Set.mem_setOf_eq,
      Metric.mem_sphere, dist_eq_norm, not_lt]
    constructor
    · intro h
      rcases h.lt_or_eq with h | h
      · exact Or.inl h
      · exact Or.inr h.symm
    · rintro (h | h)
      · exact h.le
      · exact h.ge
  have hdisj : Disjoint {x : ℂ | ρ < ‖x - ζ‖} (sphere ζ ρ) := by
    rw [Set.disjoint_left]
    intro x hx hs
    simp only [Set.mem_setOf_eq] at hx
    rw [Metric.mem_sphere, dist_eq_norm] at hs
    linarith
  have hsph : volume (sphere ζ ρ) = 0 := Measure.addHaar_sphere volume ζ ρ
  have h2 : ∫⁻ x in (ball ζ ρ)ᶜ, ENNReal.ofReal (dlambdaDensity H u x) =
      ∫⁻ x in {x | ρ < ‖x - ζ‖}, ENNReal.ofReal (dlambdaDensity H u x) := by
    rw [hcompl, lintegral_union isClosed_sphere.measurableSet hdisj,
      setLIntegral_measure_zero _ _ hsph, add_zero]
  rw [Measure.restrict_univ] at htot
  rw [← h2, ← htot, ← h1, ENNReal.add_sub_cancel_left hfin]

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ) (u : ℂ → V n) (T : ℝ)
    (htot : dlambdaEnergy H Set.univ u = ENNReal.ofReal T) (ζ : ℂ) (ρ : ℝ) :
    dlambdaEnergy H {x | ρ < ‖x - ζ‖} u = ENNReal.ofReal T - dlambdaEnergy H (ball ζ ρ) u :=
  FiniteEnergyPlane.dlambdaEnergy_norm_sub_gt_eq_sub_aux H u T htot ζ ρ
