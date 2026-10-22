-- Prove2me | solution 1 for BirkhoffGlobalSection.left_negative_closure_strict_radial_star_shaped
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T18:09:26.579531+00:00
-- url     : https://prove2.me/submissions/3847db06-f10c-4f7f-b453-29cad26178fd

import Theorems.Thm_BirkhoffGlobalSection_left_negative_closure_radial_nonpositive
import Theorems.Thm_BirkhoffGlobalSection_left_negative_closure_no_interior_radial_zero

open BirkhoffGlobalSection

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∀ s ∈ closure
      (connectedComponentIn
        {u : Phase | leviCivitaHamiltonian μ c u < 0 ∧
          0 < secondCollisionDistanceSq u}
        (fun _ : Fin 4 => (0 : ℝ))),
      ∀ a : ℝ, 0 ≤ a → a < 1 →
        leviCivitaHamiltonian μ c
          (fun i : Fin 4 => a * s i) < 0 := by
  intro s hs a ha0 ha1
  have hle :=
    left_negative_closure_radial_nonpositive μ c hμ0 hμ1 hc
      s hs a ha0 ha1
  have hne :=
    left_negative_closure_no_interior_radial_zero μ c hμ0 hμ1 hc
      s hs a ha0 ha1
  by_contra hn
  exact hne (le_antisymm hle (le_of_not_gt hn))
