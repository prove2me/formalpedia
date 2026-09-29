-- Prove2me | solution 1 for CuspidalType.IsCuspidalOfType.of_linearEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/16c874e2-7953-5a43-84eb-05c99266689a

import Definitions.Def_CuspidalType_IsCuspidalOfType
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspidalType_IsCuspidalOfType_of_linearEquiv

set_option autoImplicit false

open Polynomial CuspidalType

namespace CuStSmallRows

variable {q : ℕ} [Fact q.Prime] {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {V' : Type*} [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']

private theorem charpoly_eq_of_equivariant' {G : Type*} [Group G] (ρ : Representation K G V)
    (ρ' : Representation K G V') (e : V ≃ₗ[K] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v)) (g : G) :
    (ρ' g).charpoly = (ρ g).charpoly := by
  have hconj : ρ' g = e.conj (ρ g) := by
    apply LinearMap.ext
    intro v'
    rw [LinearEquiv.conj_apply]
    simp [he]
  rw [hconj, LinearEquiv.charpoly_conj]

end CuStSmallRows

open CuStSmallRows in

theorem solution {q : ℕ} [Fact q.Prime] {K : Type*} [Field K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {V' : Type*} [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
    {θ : (GaloisField q 2)ˣ →* Kˣ} {ρ : Representation K (GL2 q) V} {ρ' : Representation K (GL2 q) V'}
    (h : IsCuspidalOfType θ ρ) (e : V ≃ₗ[K] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v)) :
    IsCuspidalOfType θ ρ' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← e.finrank_eq]
    exact h.finrank_eq
  · intro v' hv'
    have hfix : ∀ t : ZMod q, ρ (unipotent q t) (e.symm v') = e.symm v' := by
      intro t
      apply e.injective
      rw [he, e.apply_symm_apply]
      exact hv' t
    have h0 := h.cuspidal _ hfix
    simpa using congrArg e h0
  · intro c
    apply LinearMap.ext
    intro v'
    have h1 := congrArg e (LinearMap.congr_fun (h.central c) (e.symm v'))
    rw [he, e.apply_symm_apply, LinearMap.id_apply, e.apply_symm_apply] at h1
    rw [h1, LinearMap.id_apply]
  · intro α
    rw [charpoly_eq_of_equivariant' ρ ρ' e he]
    exact h.torus_charpoly α

end S_CuspidalType_IsCuspidalOfType_of_linearEquiv
end P2MW
export P2MW.S_CuspidalType_IsCuspidalOfType_of_linearEquiv (solution)
