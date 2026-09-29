-- Prove2me | solution 1 for Farey.one_one_mem_pairs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-10T10:51:18.181+00:00
-- url     : https://prove2.me/submissions/a33c88ab-26b5-427b-927b-0362f2430586

import Definitions.Def_Farey
import Theorems.Thm_Farey_mem_pairs
import Mathlib

theorem solution {P : ℕ} (hP : 0 < P) : ((1 : ℕ), (1 : ℕ)) ∈ Farey.pairs P :=
  Farey.mem_pairs.mpr ⟨le_refl _, hP, le_refl _, le_refl _, Nat.coprime_one_left 1⟩
