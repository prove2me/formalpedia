-- Prove2me | solution 1 for BirkhoffGlobalSection.left_negative_boundary_radial_interior_negative
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T18:02:58.264348+00:00
-- url     : https://prove2.me/submissions/e590ad2d-4b7c-437c-a219-ee42ede5c134

import Theorems.Thm_BirkhoffGlobalSection_left_negative_closure_strict_radial_star_shaped
import Mathlib.Tactic

open BirkhoffGlobalSection

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∀ x : {x : Phase // x ∈ unitThreeSphere},
      ∀ r : ℝ, 0 < r →
      (fun i : Fin 4 => r * (x : Phase) i) ∈
        {s : Phase | s ∈ closure
          (connectedComponentIn
            {u : Phase | leviCivitaHamiltonian μ c u < 0 ∧
              0 < secondCollisionDistanceSq u}
            (fun _ : Fin 4 => (0 : ℝ))) ∧
          leviCivitaHamiltonian μ c s = 0 ∧
          0 < secondCollisionDistanceSq s} →
      ∀ t : ℝ, 0 ≤ t → t < r →
        leviCivitaHamiltonian μ c
          (fun i : Fin 4 => t * (x : Phase) i) < 0 := by
  intro x r hr hs t ht htr
  have hfrac0 : 0 ≤ t / r := div_nonneg ht hr.le
  have hfrac1 : t / r < 1 := (div_lt_iff₀ hr).mpr (by nlinarith)
  have hnegative :=
    left_negative_closure_strict_radial_star_shaped μ c hμ0 hμ1 hc
      (fun i : Fin 4 => r * (x : Phase) i) hs.1
      (t / r) hfrac0 hfrac1
  have heq : (fun i : Fin 4 => (t / r) * (r * (x : Phase) i)) =
      (fun i : Fin 4 => t * (x : Phase) i) := by
    funext i
    field_simp [hr.ne'] <;> ring
  simpa only [heq] using hnegative
