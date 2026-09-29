-- Prove2me | solution 1 for FourToOneGames.jointly_nae_tensor_form
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-09-24T07:36:17.516967+00:00
-- url     : https://prove2.me/submissions/eb1ecc6f-a256-4299-b2a0-227fa1ba2d1a

import Definitions.Def_FourToOneGames_NAE

set_option autoImplicit false

open FourToOneGames

/-- In `ZMod 2`, every element is idempotent. -/
theorem sq_self_zmod2 : ∀ x : ZMod 2, x * x = x := by decide

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (f : TripledSpace ι →ₗ[ZMod 2] TripledSpace ι →ₗ[ZMod 2] ZMod 2)
    (hsymm : IsSymmetricForm f)
    (φ : Fin r → TripledSpace ι →ₗ[ZMod 2] ZMod 2)
    (hφ : JointlyNAESatisfying φ)
    (hexp : ∀ x y : TripledSpace ι, f x y = ∑ j : Fin r, φ j x * φ j y) :
    NAESatisfyingForm f := by
  -- Each matrix entry of `f` expands as a sum over the tensor factors.
  have hbc : ∀ u v : ι × Fin 3,
      bilinCoeff f u v = ∑ j : Fin r, coeff (φ j) u * coeff (φ j) v := by
    intro u v
    simp only [bilinCoeff, coeff]
    exact hexp _ _
  unfold NAESatisfyingForm
  intro i
  rw [hbc, hbc, hbc, hbc, hbc, hbc]
  -- Merge the six sums into one sum over `j`.
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  -- Each per-`j` summand is exactly `NAE3` of the coefficient triple
  -- (using `x * x = x` in `ZMod 2` for the diagonal entries).
  have hmain : (∑ j : Fin r, (((((coeff (φ j) (i, 0) * coeff (φ j) (i, 0)
      + coeff (φ j) (i, 1) * coeff (φ j) (i, 1))
      + coeff (φ j) (i, 2) * coeff (φ j) (i, 2))
      + coeff (φ j) (i, 0) * coeff (φ j) (i, 1))
      + coeff (φ j) (i, 1) * coeff (φ j) (i, 2))
      + coeff (φ j) (i, 2) * coeff (φ j) (i, 0)))
      = ∑ j : Fin r, NAE3 (coeff (φ j) (i, 0)) (coeff (φ j) (i, 1))
          (coeff (φ j) (i, 2)) :=
    Finset.sum_congr rfl (fun j _ => by unfold NAE3; simp only [sq_self_zmod2])
  rw [hmain]
  unfold JointlyNAESatisfying at hφ
  exact hφ i
