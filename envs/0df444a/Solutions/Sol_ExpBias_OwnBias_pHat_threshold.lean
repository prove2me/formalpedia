-- Prove2me | solution 1 for ExpBias.OwnBias.pHat_threshold
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T19:57:19.921934+00:00
-- url     : https://prove2.me/submissions/458f3fa9-b89a-4bce-9362-05525702c2c0

import Mathlib
import Definitions.Def_ExpBias_OwnBias_Model
open ExpBias.OwnBias

theorem solution(P : Params) (hP : P.Standing) :
    0 < pHat P ∧ pHat P < 1 ∧
      (P.vS ≤ P.p * P.vW + (1 - P.p) * P.vN ↔ pHat P ≤ P.p) := by
  obtain ⟨h1, h2, h3, h4, _, _⟩ := hP
  unfold pHat
  have hd : 0 < P.vW - P.vN := by linarith
  refine ⟨div_pos (by linarith) hd, (div_lt_one hd).2 (by linarith), ?_⟩
  rw [div_le_iff₀ hd]
  constructor <;> intro h <;> nlinarith
