-- Prove2me | solution 1 for BirkhoffGlobalSection.left_negative_boundary_unique_ray_scale
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T17:44:35.781474+00:00
-- url     : https://prove2.me/submissions/ed703680-fb0f-480e-ba43-9cf3c05f8b84

import Theorems.Thm_BirkhoffGlobalSection_left_negative_boundary_radial_interior_negative
import Mathlib.Tactic.Linarith

open BirkhoffGlobalSection

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∀ x : {x : Phase // x ∈ unitThreeSphere},
      ∀ r t : ℝ, 0 < r → 0 < t →
      (fun i : Fin 4 => r * (x : Phase) i) ∈
        {s : Phase | s ∈ closure
          (connectedComponentIn
            {u : Phase | leviCivitaHamiltonian μ c u < 0 ∧
              0 < secondCollisionDistanceSq u}
            (fun _ : Fin 4 => (0 : ℝ))) ∧
          leviCivitaHamiltonian μ c s = 0 ∧
          0 < secondCollisionDistanceSq s} →
      (fun i : Fin 4 => t * (x : Phase) i) ∈
        {s : Phase | s ∈ closure
          (connectedComponentIn
            {u : Phase | leviCivitaHamiltonian μ c u < 0 ∧
              0 < secondCollisionDistanceSq u}
            (fun _ : Fin 4 => (0 : ℝ))) ∧
          leviCivitaHamiltonian μ c s = 0 ∧
          0 < secondCollisionDistanceSq s} →
      r = t := by
  intro x r t hr ht hsr hst
  rcases lt_trichotomy r t with hlt | heq | hgt
  · have hneg := left_negative_boundary_radial_interior_negative
      μ c hμ0 hμ1 hc x t ht hst r hr.le hlt
    have hzero : leviCivitaHamiltonian μ c
        (fun i : Fin 4 => r * (x : Phase) i) = 0 := hsr.2.1
    linarith
  · exact heq
  · have hneg := left_negative_boundary_radial_interior_negative
      μ c hμ0 hμ1 hc x r hr hsr t ht.le hgt
    have hzero : leviCivitaHamiltonian μ c
        (fun i : Fin 4 => t * (x : Phase) i) = 0 := hst.2.1
    linarith
