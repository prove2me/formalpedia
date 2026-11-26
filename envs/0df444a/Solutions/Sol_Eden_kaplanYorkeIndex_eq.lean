-- Prove2me | solution 1 for Eden.kaplanYorkeIndex_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:51:16.652948+00:00
-- url     : https://prove2.me/submissions/255c143a-6f2a-4bb2-a761-b297abf04a65

import Definitions.Def_Eden_LyapunovExponents
import Mathlib.Data.Finset.Max
import Definitions.Def_Eden_KaplanYorke
import Theorems.Thm_Eden_kaplanYorkeIndex_mem
import Theorems.Thm_Eden_le_kaplanYorkeIndex

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {a : Fin 5 → ℝ} {j : ℕ} (hj : j ≤ 5)
    (hs : 0 ≤ spectrumPartialSum a j)
    (hafter : ∀ k, j < k → k ≤ 5 → spectrumPartialSum a k < 0) :
    kaplanYorkeIndex a = j := by
  apply le_antisymm
  · by_contra h
    have hi := kaplanYorkeIndex_mem a
    exact (not_lt_of_ge hi.2) (hafter _ (lt_of_not_ge h) hi.1)
  · exact le_kaplanYorkeIndex hj hs
end Eden
