-- Prove2me | solution 1 for BookProof.QgOuterFock.sum_reindex_particles
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T05:12:21.309491+00:00
-- url     : https://prove2.me/submissions/6d2405c0-bf1b-4931-9eeb-ecaff443d685

import Mathlib
import Definitions.Def_ChapterQgOuterFockEsa
open BookProof.QgOuterFock

theorem solution {n : ℕ} {α : Type*} [AddCommMonoid α] (F : Fin (n * 84) → α) :
    ∑ I : Fin (n * 84), F I = ∑ p : Fin n, ∑ j : Fin 84, F (pcoord p j) := by
  rw [← Equiv.sum_comp finProdFinEquiv]
  rw [Fintype.sum_prod_type (fun ij : Fin n × Fin 84 => F (finProdFinEquiv ij))]
  simp [pcoord]
