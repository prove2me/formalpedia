-- Prove2me | solution 1 for BookProof.ChapterGravityProjDirectSum.isCompl_range_of_add_eq_id
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:27:55.959133+00:00
-- url     : https://prove2.me/submissions/4d954222-e7d2-44a3-a9ad-26954f7880f7

-- Generated from ChapterGravityProjDirectSum.lean — solution of BookProof.ChapterGravityProjDirectSum.isCompl_range_of_add_eq_id
import Mathlib
import Definitions.Def_ChapterGravityProjDirectSum
import Definitions.Def_ChapterGravityProjector
import Definitions.Def_ChapterGravityTimeProj
open BookProof.ChapterGravityProjDirectSum



open Matrix


open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityTimeProj

set_option maxHeartbeats 1000000 in
theorem solution {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (P Q : V →ₗ[R] V) (hsum : P + Q = LinearMap.id)
    (hPQ : P.comp Q = 0) (hQP : Q.comp P = 0) :
    IsCompl (LinearMap.range P) (LinearMap.range Q) := by

  have hx : ∀ x : V, P x + Q x = x := by
    intro x
    have := congrArg (fun L : V →ₗ[R] V => L x) hsum
    simpa using this
  constructor
  · rw [Submodule.disjoint_def]
    rintro x ⟨a, rfl⟩ ⟨b, hb⟩
    have h1 : Q (P a) = 0 := congrArg (fun L : V →ₗ[R] V => L a) hQP
    have h2 : P (P a) = P a := by
      have := hx (P a)
      rw [h1] at this
      simpa using this
    have h3 : P (P a) = 0 := by
      rw [← hb]
      exact congrArg (fun L : V →ₗ[R] V => L b) hPQ
    rw [h2] at h3
    exact h3
  · rw [codisjoint_iff_le_sup]
    intro x _
    exact Submodule.mem_sup.2 ⟨P x, ⟨x, rfl⟩, Q x, ⟨x, rfl⟩, hx x⟩
