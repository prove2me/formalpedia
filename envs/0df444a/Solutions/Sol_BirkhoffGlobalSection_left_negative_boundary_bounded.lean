-- Prove2me | solution 1 for BirkhoffGlobalSection.left_negative_boundary_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T17:44:23.538218+00:00
-- url     : https://prove2.me/submissions/ab88c0b6-872e-4ff7-812c-1fca3d0e8fe3

import Theorems.Thm_BirkhoffGlobalSection_left_negative_closure_bounded

open BirkhoffGlobalSection

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    Bornology.IsBounded
      {s : Phase | s ∈ closure
        (connectedComponentIn
          {t : Phase | leviCivitaHamiltonian μ c t < 0 ∧
            0 < secondCollisionDistanceSq t}
          (fun _ : Fin 4 => (0 : ℝ))) ∧
        leviCivitaHamiltonian μ c s = 0 ∧
        0 < secondCollisionDistanceSq s} := by
  apply (left_negative_closure_bounded μ c hμ0 hμ1 hc).subset
  intro s hs
  exact hs.1
