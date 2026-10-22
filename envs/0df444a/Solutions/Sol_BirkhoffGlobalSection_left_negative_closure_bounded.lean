-- Prove2me | solution 1 for BirkhoffGlobalSection.left_negative_closure_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T18:02:56.497372+00:00
-- url     : https://prove2.me/submissions/9b95ed9f-5a9b-4ee2-879b-c7b7ab8b374e

import Mathlib
import Theorems.Thm_BirkhoffGlobalSection_left_negative_closure_position_coordinates_bounded
import Theorems.Thm_BirkhoffGlobalSection_left_negative_closure_momentum_coordinates_bounded

open BirkhoffGlobalSection

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    Bornology.IsBounded
      (closure
        (connectedComponentIn
          {t : Phase | leviCivitaHamiltonian μ c t < 0 ∧
            0 < secondCollisionDistanceSq t}
          (fun _ : Fin 4 => (0 : ℝ)))) := by
  obtain ⟨R, hR⟩ :=
    left_negative_closure_position_coordinates_bounded μ c hμ0 hμ1 hc
  obtain ⟨M, hM⟩ :=
    left_negative_closure_momentum_coordinates_bounded μ c hμ0 hμ1 hc
  let T : Fin 4 → Set ℝ := fun _ => Set.Icc (-(max R M)) (max R M)
  have hbox : Bornology.IsBounded (Set.pi Set.univ T) :=
    Bornology.IsBounded.pi (fun _ => Metric.isBounded_Icc _ _)
  apply hbox.subset
  intro s hs
  intro i _
  have hcoord : ∀ i : Fin 4, |s i| ≤ max R M := by
    intro j
    fin_cases j
    · exact (hR s hs).1.trans (le_max_left R M)
    · exact (hR s hs).2.trans (le_max_left R M)
    · exact (hM s hs).1.trans (le_max_right R M)
    · exact (hM s hs).2.trans (le_max_right R M)
  exact abs_le.mp (hcoord i)
