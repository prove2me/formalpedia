-- Prove2me | solution 1 for BirkhoffGlobalSection.birkhoff_far_arc_degeneration
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-25T15:21:05.461041+00:00
-- url     : https://prove2.me/submissions/74a0d198-37c4-4c56-9364-0c05f06f0de8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_BirkhoffShootingArcs
import Mathlib.Tactic
import Theorems.Thm_BirkhoffGlobalSection_birkhoff_far_arc_limit
import Theorems.Thm_BirkhoffGlobalSection_birkhoff_far_limit_end

open BirkhoffGlobalSection

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (b : ℝ) (hb : 0 < b)
    (hgood : ∀ r ∈ Set.Ioo 0 b, ∃ x : LeftEnergyState μ c, (x : Phase) = farShootingStart μ c r ∧ ∃ τ : ℝ, IsFarShootingArc φ x τ)
    (hbad : ¬ (∃ x : LeftEnergyState μ c, (x : Phase) = farShootingStart μ c b ∧ ∃ τ : ℝ, IsFarShootingArc φ x τ)) :
    ∃ xb : LeftEnergyState μ c, (xb : Phase) = farShootingStart μ c b ∧ ∃ T : ℝ, 0 < T ∧
      (∀ u ∈ Set.Ioo 0 T, relativePosition μ ((φ u xb : LeftEnergyState μ c) : Phase) 1 < 0) ∧
      (∀ u ∈ Set.Ioo 0 T,
        0 < jacobiVelocity (leviCivitaToJacobi μ ((φ u xb : LeftEnergyState μ c) : Phase)) 0) ∧
      relativePosition μ ((φ T xb : LeftEnergyState μ c) : Phase) 0 = 0 ∧
      ((((φ T xb : LeftEnergyState μ c) : Phase) 0 = 0 ∧ ((φ T xb : LeftEnergyState μ c) : Phase) 1 = 0) ∨
        (relativePosition μ ((φ T xb : LeftEnergyState μ c) : Phase) 1 < 0 ∧
          jacobiVelocity (leviCivitaToJacobi μ ((φ T xb : LeftEnergyState μ c) : Phase)) 0 = 0 ∧
          jacobiVelocity (leviCivitaToJacobi μ ((φ T xb : LeftEnergyState μ c) : Phase)) 1 ≠ 0)) ∧
      ∀ η > 0, ∃ δ > 0, ∀ r ∈ Set.Ioo (b - δ) b, ∀ x : LeftEnergyState μ c, ∀ τ : ℝ,
        (x : Phase) = farShootingStart μ c r → IsFarShootingArc φ x τ → |τ - T| < η := by
  obtain ⟨xb, hxb, hv, T, hT, hcl, hvx, hP, hX, hY, hVxT, htan, hconv⟩ :=
    birkhoff_far_arc_limit μ c hμ0 hμ1 hc φ hφ b hb hgood hbad
  have hb0 : (xb : Phase) 0 = 0 := by rw [hxb]; simp [farShootingStart]
  have hb1 : (xb : Phase) 1 = b := by rw [hxb]; simp [farShootingStart]
  have hno : ¬ ∃ τ : ℝ, IsFarShootingArc φ xb τ := fun h => hbad ⟨xb, hxb, h⟩
  obtain ⟨hopen, hend⟩ := birkhoff_far_limit_end μ c hμ0 hμ1 hc φ hφ xb T hT hb0
    (by rw [hb1]; exact hb) hv hcl hvx hP hX hY hVxT hno
  refine ⟨xb, hxb, T, hT, hopen, hvx, hX, ?_, hconv⟩
  rcases hend with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2, htan h1 h2⟩
