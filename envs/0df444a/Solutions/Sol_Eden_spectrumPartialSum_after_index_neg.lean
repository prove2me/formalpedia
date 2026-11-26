-- Prove2me | solution 1 for Eden.spectrumPartialSum_after_index_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:47:34.751428+00:00
-- url     : https://prove2.me/submissions/c755b38c-a646-421c-9651-80fd0589d575

import Definitions.Def_Eden_LyapunovExponents
import Mathlib.Data.Finset.Max
import Definitions.Def_Eden_KaplanYorke
import Theorems.Thm_Eden_le_kaplanYorkeIndex

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {a : Fin 5 → ℝ} {k : ℕ}
    (hk : kaplanYorkeIndex a < k) (hk₅ : k ≤ 5) : spectrumPartialSum a k < 0 := by
  by_contra h
  exact (not_le_of_gt hk) (le_kaplanYorkeIndex hk₅ (le_of_not_gt h))
end Eden
