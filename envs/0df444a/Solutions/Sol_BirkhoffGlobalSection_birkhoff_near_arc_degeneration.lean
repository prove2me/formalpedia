-- Prove2me | solution 1 for BirkhoffGlobalSection.birkhoff_near_arc_degeneration
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-25T15:21:04.005419+00:00
-- url     : https://prove2.me/submissions/5cbee85c-dde6-4c2a-a1fc-232fcc014fc6

import Definitions.Def_BirkhoffShootingArcs
import Mathlib.Tactic
import Theorems.Thm_BirkhoffGlobalSection_birkhoff_near_arc_limit
import Theorems.Thm_BirkhoffGlobalSection_birkhoff_near_limit_collision

open BirkhoffGlobalSection

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (b : ℝ) (hb : 0 < b)
    (hgood : ∀ r ∈ Set.Ioo 0 b, ∃ x : LeftEnergyState μ c, (x : Phase) = nearShootingStart μ c r ∧ ∃ τ : ℝ, IsNearShootingArc φ x τ)
    (hbad : ¬ (∃ x : LeftEnergyState μ c, (x : Phase) = nearShootingStart μ c b ∧ ∃ τ : ℝ, IsNearShootingArc φ x τ)) :
    ∃ xb : LeftEnergyState μ c, (xb : Phase) = nearShootingStart μ c b ∧ ∃ T : ℝ, 0 < T ∧
      (∀ t ∈ Set.Ioo (-T) 0,
        0 < relativePosition μ ((φ t xb : LeftEnergyState μ c) : Phase) 0 ∧
        relativePosition μ ((φ t xb : LeftEnergyState μ c) : Phase) 1 < 0) ∧
      ((φ (-T) xb : LeftEnergyState μ c) : Phase) 0 = 0 ∧
      ((φ (-T) xb : LeftEnergyState μ c) : Phase) 1 = 0 ∧
      ∀ η > 0, ∃ δ > 0, ∀ r ∈ Set.Ioo (b - δ) b, ∀ x : LeftEnergyState μ c, ∀ τ : ℝ,
        (x : Phase) = nearShootingStart μ c r → IsNearShootingArc φ x τ → |τ - T| < η := by
  obtain ⟨xb, hxb, hv, T, hT, hcl, hP, hX, hY, hconv⟩ :=
    birkhoff_near_arc_limit μ c hμ0 hμ1 hc φ hφ b hb hgood hbad
  have hb0 : (xb : Phase) 0 = b := by rw [hxb]; simp [nearShootingStart]
  have hb1 : (xb : Phase) 1 = 0 := by rw [hxb]; simp [nearShootingStart]
  have hb2 : (xb : Phase) 2 = 0 := by rw [hxb]; simp [nearShootingStart]
  have hno : ¬ ∃ τ : ℝ, IsNearShootingArc φ xb τ := fun h => hbad ⟨xb, hxb, h⟩
  obtain ⟨hopen, hc0, hc1⟩ := birkhoff_near_limit_collision μ c hμ0 hμ1 hc φ hφ xb T hT hb1 hb2
    (by rw [hb0]; exact hb) hv hcl hP hX hY hno
  exact ⟨xb, hxb, T, hT, hopen, hc0, hc1, hconv⟩
