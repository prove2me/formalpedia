-- Prove2me | solution 1 for ErschlerZheng.not_satisfiesFr_three_firstString
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T11:44:25.689745+00:00
-- url     : https://prove2.me/submissions/b0dcb2b8-f31d-4035-9a66-552d52babf67

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk

section
/-!
# A17: `(012)^∞` does not satisfy `Fr(3)` (p. 34)

A block of length 3 can only start a `201`/`211` window at offset `m = 0`, and the first block
of `(012)^∞` begins with `0`.
-/

namespace ErschlerZheng

end ErschlerZheng
end

section
open ErschlerZheng
theorem solution : ¬ SatisfiesFr 3 firstString := by
  intro h
  obtain ⟨m, hm, h2, -, -⟩ := h 0
  have hm0 : m = 0 := by omega
  subst hm0
  simp [firstString] at h2
end
