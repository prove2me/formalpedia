-- Prove2me | solution 1 for BookProof.SmOneParticle.smG_injective
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:17:43.99409+00:00
-- url     : https://prove2.me/submissions/47d69b91-00b5-4055-a79d-15e876949e23

-- Generated from ChapterSmOneParticle.lean — theorem BookProof.SmOneParticle.smG_injective
import Mathlib
import Definitions.Def_ChapterSmOneParticle
open BookProof.SmOneParticle
open BookProof.SmOneParticle

theorem solution: Function.Injective fun p : Fin 8 × Fin 3 => smG p.1 p.2 := by
  intro p q h
  simp only [smG, EmbeddingLike.apply_eq_iff_eq, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at h
  exact Prod.ext h.1 h.2
