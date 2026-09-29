-- Prove2me | solution 1 for BookProof.YangMillsBianchi.bianchi
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T02:22:34.001815+00:00
-- url     : https://prove2.me/submissions/a82ffe31-3942-4b3a-9620-1114dd473123

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
