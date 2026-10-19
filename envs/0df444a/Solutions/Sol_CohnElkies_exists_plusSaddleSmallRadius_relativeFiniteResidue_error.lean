-- Prove2me | solution 1 for CohnElkies.exists_plusSaddleSmallRadius_relativeFiniteResidue_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.275309+00:00
-- url     : https://prove2.me/submissions/cca21a49-084c-4282-a6d2-5f474bd51cd2

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_exists_plusSaddleSmallRadius_finiteResidue_error

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ε : ℝ}
    (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ℓ : ℝ), 0 < ℓ →
        ∀ N : ℕ, 2 * (N : ℝ) ≤ ℓ →
          ∀ y : ℝ, 0 ≤ y →
            2 * y ≤ (N : ℝ) + 2 →
              Real.exp y *
                |(∑ n ∈ Finset.range (N + 1),
                    ((-y) ^ n / (n.factorial : ℝ)) *
                      plusSaddleSmallRadiusCoefficient ε ℓ n) -
                  Real.exp (-y)| ≤
                (C / ℓ) *
                  Real.exp (C * (N : ℝ) ^ 2 / ℓ) *
                    (2 * y + y ^ 2) * Real.exp (2 * y) +
                2 * Real.exp y *
                  (y ^ (N + 1) /
                    ((N + 1).factorial : ℝ)) := by
  obtain ⟨C, hC, hfinite⟩ :=
    exists_plusSaddleSmallRadius_finiteResidue_error
      hε horder
  refine ⟨C, hC, ?_⟩
  intro ℓ hℓ N hN y hy hyratio
  have hbound := hfinite ℓ hℓ N hN y hy hyratio
  have hexp : 0 ≤ Real.exp y := (Real.exp_pos y).le
  calc
    Real.exp y *
        |(∑ n ∈ Finset.range (N + 1),
            ((-y) ^ n / (n.factorial : ℝ)) *
              plusSaddleSmallRadiusCoefficient ε ℓ n) -
          Real.exp (-y)| ≤
      Real.exp y *
        ((C / ℓ) *
          Real.exp (C * (N : ℝ) ^ 2 / ℓ) *
            (2 * y + y ^ 2) * Real.exp y +
          2 * (y ^ (N + 1) /
            ((N + 1).factorial : ℝ))) :=
          mul_le_mul_of_nonneg_left hbound hexp
    _ = (C / ℓ) *
          Real.exp (C * (N : ℝ) ^ 2 / ℓ) *
            (2 * y + y ^ 2) * Real.exp (2 * y) +
          2 * Real.exp y *
            (y ^ (N + 1) /
              ((N + 1).factorial : ℝ)) := by
          rw [show Real.exp (2 * y) =
            Real.exp y * Real.exp y by
              rw [show 2 * y = y + y by ring,
                Real.exp_add]]
          ring
end CohnElkies
