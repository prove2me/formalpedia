-- Prove2me | solution 1 for BookProof.ChapterMackeyGeneralBase.cocycle_mem_stabilizer
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T06:42:40.06602+00:00
-- url     : https://prove2.me/submissions/9fdafc99-1f8d-458d-8db4-5e83200c0fa9

import Mathlib
import Definitions.Def_ChapterMackeyGeneralBase
import Definitions.Def_ChapterMackeyImprimitivity
import Definitions.Def_ChapterA4

set_option autoImplicit false

open BookProof.ChapterMackeyGeneralBase in
theorem solution {G : Type*} [Group G] {X : Type*} [MulAction G X] {x₀ : X} {s : X → G}
    (hs : ∀ x, s x • x₀ = x) (g : G) (x : X) :
    cocycle s g x ∈ MulAction.stabilizer G x₀ := by
  rw [MulAction.mem_stabilizer_iff, cocycle, mul_smul, mul_smul, hs, smul_inv_smul,
    inv_smul_eq_iff, hs]
