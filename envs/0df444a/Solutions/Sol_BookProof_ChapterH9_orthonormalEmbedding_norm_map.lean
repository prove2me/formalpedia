-- Prove2me | solution 1 for BookProof.ChapterH9.orthonormalEmbedding_norm_map
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T01:33:08.289212+00:00
-- url     : https://prove2.me/submissions/0ef678bb-47cb-4195-91d2-d64d3045704f

import Definitions.Def_ChapterH8Bases

open BookProof.ChapterH8

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem solution {m : ℕ} (w : Fin m → E) (hw : Orthonormal ℂ w)
    (x : EuclideanSpace ℂ (Fin m)) : ‖orthonormalEmbedding w hw x‖ = ‖x‖ := by
  exact (orthonormalEmbeddingLI w hw).norm_map x

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms solution
