-- Prove2me | solution 1 for BookProof.ChapterSphericalBesselODE.gIter_ode
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:28:33.931544+00:00
-- url     : https://prove2.me/submissions/775b9466-9366-4868-9fe1-786e9bd4b87f

-- Generated from ChapterSphericalBesselODE.lean — solution of BookProof.ChapterSphericalBesselODE.gIter_ode
import Mathlib
import Definitions.Def_ChapterSphericalBesselODE
import Theorems.Thm_BookProof_ChapterSphericalBesselODE_diffAt_gIter
import Theorems.Thm_BookProof_ChapterSphericalBesselODE_diffAt_deriv_gIter
import Theorems.Thm_BookProof_ChapterSphericalBesselODE_deriv_gIter_eq
import Theorems.Thm_BookProof_ChapterSphericalBesselODE_second_deriv_gIter
import Theorems.Thm_BookProof_ChapterSphericalBesselODE_gIter_ode_zero
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalBesselODE




open BookProof.ChapterSphericalBessel

set_option maxHeartbeats 1000000 in
theorem solution (l : ℕ) {r : ℝ} (hr : r ≠ 0) :
    r * deriv (deriv (gIter l)) r + (2 * l + 2) * deriv (gIter l) r + r * gIter l r = 0 := by

  induction l generalizing r with
  | zero => simpa using gIter_ode_zero hr
  | succ n ih =>
      -- the first-order identity `gₙ = (2n+3) gₙ₊₁ + r gₙ₊₁'`, valid on the punctured line
      have key : ∀ x : ℝ, x ≠ 0 →
          gIter n x = (2 * n + 3) * gIter (n + 1) x + x * deriv (gIter (n + 1)) x := by
        intro x hx
        have hIH := ih hx
        rw [second_deriv_gIter n hx, deriv_gIter_eq n hx] at hIH
        have hx0 : x * (gIter n x
            - ((2 * n + 3) * gIter (n + 1) x + x * deriv (gIter (n + 1)) x)) = 0 := by
          nlinarith [hIH]
        rcases mul_eq_zero.mp hx0 with h0 | h0
        · exact absurd h0 hx
        · linarith
      have hEq : gIter n =ᶠ[nhds r]
          fun x => (2 * (n : ℝ) + 3) * gIter (n + 1) x + x * deriv (gIter (n + 1)) x := by
        filter_upwards [isOpen_ne.mem_nhds hr] with x hx using key x hx
      have hD : HasDerivAt
          (fun x : ℝ => (2 * (n : ℝ) + 3) * gIter (n + 1) x + x * deriv (gIter (n + 1)) x)
          ((2 * (n : ℝ) + 3) * deriv (gIter (n + 1)) r
            + (1 * deriv (gIter (n + 1)) r + r * deriv (deriv (gIter (n + 1))) r)) r :=
        HasDerivAt.add (((diffAt_gIter (n + 1) hr).hasDerivAt).const_mul _)
          ((hasDerivAt_id r).mul ((diffAt_deriv_gIter (n + 1) hr).hasDerivAt))
      have hfin : deriv (gIter n) r = (2 * (n : ℝ) + 3) * deriv (gIter (n + 1)) r
          + (1 * deriv (gIter (n + 1)) r + r * deriv (deriv (gIter (n + 1))) r) := by
        rw [hEq.deriv_eq, hD.deriv]
      rw [deriv_gIter_eq n hr] at hfin
      push_cast
      linarith
