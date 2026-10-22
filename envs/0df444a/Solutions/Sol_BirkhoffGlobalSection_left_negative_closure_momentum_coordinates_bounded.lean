-- Prove2me | solution 1 for BirkhoffGlobalSection.left_negative_closure_momentum_coordinates_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T18:09:26.422979+00:00
-- url     : https://prove2.me/submissions/9bde6caa-fa13-4f07-9791-9cd8ec776a61

import Theorems.Thm_BirkhoffGlobalSection_left_negative_closure_position_coordinates_bounded
import Theorems.Thm_BirkhoffGlobalSection_left_negative_closure_uniform_collision_gap
import Theorems.Thm_BirkhoffGlobalSection_left_negative_closure_nonpositive_energy
import Theorems.Thm_BirkhoffGlobalSection_nonpositive_regular_energy_momentum_bound

open BirkhoffGlobalSection

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∃ R : ℝ, ∀ s ∈ closure
      (connectedComponentIn
        {t : Phase | leviCivitaHamiltonian μ c t < 0 ∧
          0 < secondCollisionDistanceSq t}
        (fun _ : Fin 4 => (0 : ℝ))),
      |s 2| ≤ R ∧ |s 3| ≤ R := by
  obtain ⟨P, hP⟩ :=
    left_negative_closure_position_coordinates_bounded μ c hμ0 hμ1 hc
  obtain ⟨δ, hδ, hgap⟩ :=
    left_negative_closure_uniform_collision_gap μ c hμ0 hμ1 hc
  obtain ⟨M, hM⟩ :=
    nonpositive_regular_energy_momentum_bound μ c P δ hδ
  refine ⟨M, ?_⟩
  intro s hs
  exact hM s (hP s hs).1 (hP s hs).2 (hgap s hs)
    (left_negative_closure_nonpositive_energy μ c hμ0 hμ1 hc s hs)
