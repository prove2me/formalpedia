-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DiffFarisLavine.diffMaxN_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:06:00.11955+00:00
-- url     : https://prove2.me/submissions/3b2fc5a0-df76-4354-8017-181fe32536ae

-- Adapted from Leonardo Pedro, timepiece commit 61595bc, Apache-2.0.
-- https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesDiffFarisLavine.lean
import Definitions.Def_ChapterNavierStokesDiffFarisLavine
import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 4000000
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.DiffFarisLavine
open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine
open BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ThreeComponent
open BookProof.NavierStokesFlow.CanonicalVector BookProof.NavierStokesFlow.DifferentialL2

private theorem diffN_apply (mu : ℝ) (z : maxDom (velSym mu)) :
    diffMaxN mu (diffMaxEquiv mu z) = velUnitary ((diagMax (velSym mu) z : L2I Vel)) := by
  simp only [diffMaxN, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  rfl

private theorem diffE_coe (mu : ℝ) (z : maxDom (velSym mu)) :
    ((diffMaxEquiv mu z : diffMaxDom mu) : L2d 3) = velUnitary ((z : L2I Vel)) := rfl

theorem solution (mu : ℝ) : SymmetricOn (diffMaxDom mu) (diffMaxN mu) := by
  intro z w
  obtain ⟨z', rfl⟩ := (diffMaxEquiv mu).surjective z
  obtain ⟨w', rfl⟩ := (diffMaxEquiv mu).surjective w
  rw [diffN_apply, diffN_apply, diffE_coe, diffE_coe,
    velUnitary.inner_map_map, velUnitary.inner_map_map]
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun k => ?_
  simp only [RCLike.inner_apply, IkebeKato.diagMax_coe, map_mul, Complex.conj_ofReal]
  ring

#print axioms solution
