-- Prove2me | solution 1 for BookProof.ChapterH9.coordIncl_norm_map
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T01:33:09.384678+00:00
-- url     : https://prove2.me/submissions/ce71a203-6180-4a3b-9d56-6f6da1ed3086

import Definitions.Def_ChapterH8Bases

open BookProof.ChapterH8

theorem solution {m n : ℕ} (hmn : m ≤ n) (x : EuclideanSpace ℂ (Fin m)) :
    ‖coordIncl hmn x‖ = ‖x‖ := by
  unfold coordIncl orthonormalEmbedding
  exact LinearIsometry.norm_map _ x

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms solution
