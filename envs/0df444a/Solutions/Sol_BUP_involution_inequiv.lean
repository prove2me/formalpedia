-- Prove2me | solution 1 for BUP.involution_inequiv
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T01:06:05.956459+00:00
-- url     : https://prove2.me/submissions/537b5ee0-0038-4241-9b27-0247b71e3f2c

import Mathlib
import Definitions.Def_BUP_alg
import Definitions.Def_BUP_tor
open BUP

theorem solution {A1 B1 P1 Bg1 A2 B2 P2 Bg2 : Type*} [Group A1] [Group B1] [Group P1]
    [Group Bg1] [Group A2] [Group B2] [Group P2] [Group Bg2]
    (W1 : TorusWorld A1 B1 P1 Bg1) (W2 : TorusWorld A2 B2 P2 Bg2)
    (hab : ∀ x y : B1, x * y = y * x)
    (hnb : ∃ x y : B2, x * y ≠ y * x) :
    ¬ (∃ eA : A1 ≃* A2, ∃ eB : B1 ≃* B2,
      (∀ a : A1, eB (W1.C.inj a) = W2.C.inj (eA a)) ∧
      (∀ b : B1, W2.C.proj (eB b) = W1.C.proj b)) := by
  rintro ⟨eA, eB, -, -⟩
  obtain ⟨x, y, hxy⟩ := hnb
  apply hxy
  have := hab (eB.symm x) (eB.symm y)
  have := congrArg eB this
  simpa using this
