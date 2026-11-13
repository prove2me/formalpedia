-- Prove2me | solution 1 for CombOpt.Circulation.theorem_3_15
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @0xbf
-- created : 2026-11-12T14:09:23.749418+00:00
-- url     : https://prove2.me/submissions/8717b0d6-e744-4fd2-9d84-af2dc198659f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_CombOpt_Circulation_solution38_implies_Gale_conditions
import Theorems.Thm_CombOpt_Circulation_gale_conditions_imply_solution38

open CombOpt.Circulation

theorem solution {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : MultiDigraph V E) (u : E → ℝ) (hu : ∀ e, 0 ≤ u e) (b : V → ℝ) :
    ((∃ x, IsSolution38 G u b x) ↔
      ((∑ v, b v = 0) ∧
        ∀ A : Finset V, ∑ v ∈ A, b v ≤ ∑ e ∈ delta G Aᶜ, u e)) ∧
      (IsIntegralVector b → IsIntegralVector u →
        ((∃ x, IsIntegralVector x ∧ IsSolution38 G u b x) ↔
          ((∑ v, b v = 0) ∧
            ∀ A : Finset V, ∑ v ∈ A, b v ≤ ∑ e ∈ delta G Aᶜ, u e))) := by
  constructor
  · constructor
    · rintro ⟨x, hx⟩
      exact solution38_implies_Gale_conditions G u b x hx
    · intro hcond
      exact (gale_conditions_imply_solution38 G u hu b hcond).1
  · intro hb huInt
    constructor
    · rintro ⟨x, hxInt, hx⟩
      exact solution38_implies_Gale_conditions G u b x hx
    · intro hcond
      exact (gale_conditions_imply_solution38 G u hu b hcond).2 hb huInt
