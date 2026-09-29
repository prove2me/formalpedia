-- Prove2me | solution 1 for FourToOneGames.tensor_decomposition_jointly_nae
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-09-24T07:45:57.183608+00:00
-- url     : https://prove2.me/submissions/96e4b461-5364-4280-a080-321e5aeed654

import Definitions.Def_FourToOneGames_NAE

set_option autoImplicit false

open FourToOneGames

/-- In `ZMod 2`, every element is idempotent. -/
theorem sq_self_zmod2 : ∀ x : ZMod 2, x * x = x := by decide

-- FourToOneGames.tensor_decomposition_jointly_nae (Proposition 4.13):
-- a tensor decomposition of an NAE-satisfying form is jointly NAE-satisfying.
-- Converse of the rank-2 node: expand each matrix entry of `f` via the
-- tensor decomposition, rewrite the NAE-satisfying equation, and read off
-- the joint-NAE sum (using `x * x = x` in `ZMod 2` on the diagonal entries).
theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (f : TripledSpace ι →ₗ[ZMod 2] TripledSpace ι →ₗ[ZMod 2] ZMod 2)
    (hsymm : IsSymmetricForm f) (hnae : NAESatisfyingForm f)
    (φ : Fin r → TripledSpace ι →ₗ[ZMod 2] ZMod 2)
    (hdec : IsTensorDecomposition f φ) :
    JointlyNAESatisfying φ := by
  obtain ⟨_, hexp⟩ := hdec
  -- Each matrix entry of `f` expands as a sum over the tensor factors.
  have hbc : ∀ u v : ι × Fin 3,
      bilinCoeff f u v = ∑ j : Fin r, coeff (φ j) u * coeff (φ j) v := by
    intro u v
    simp only [bilinCoeff, coeff]
    exact hexp _ _
  unfold JointlyNAESatisfying
  intro i
  have h := hnae i
  rw [hbc, hbc, hbc, hbc, hbc, hbc] at h
  -- Merge the six sums into one sum over `j`.
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib] at h
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
  rw [hmain] at h
  exact h
