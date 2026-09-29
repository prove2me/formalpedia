-- Prove2me | solution 2 for BookProof.YangMillsBianchi.bianchi
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T02:23:00.67145+00:00
-- url     : https://prove2.me/submissions/db3c356b-00fd-4a17-8e6f-e17217760974

-- Generated from ChapterYangMillsBianchi.lean — solution of BookProof.YangMillsBianchi.bianchi
import Mathlib.Tactic.NoncommRing
import Mathlib
import Definitions.Def_ChapterYangMillsBianchi
open BookProof.YangMillsBianchi










open BigOperators



variable {R : Type*} [Ring R]

set_option maxHeartbeats 1000000 in
theorem solution (D : Fin 3 → R) :
    ∑ i, ∑ j, ∑ k, (eps i j k) • ⁅D i, ⁅D j, D k⁆⁆ = 0 := by

  simp [ Fin.sum_univ_three, eps ];
  simp [ Int.sign ];
  simp only [Bracket.bracket]
  noncomm_ring
