-- Prove2me | solution 1 for Eden.spectrumEntry_at_kaplanYorkeIndex_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:50:22.474561+00:00
-- url     : https://prove2.me/submissions/4c57f2b8-ba45-4e23-9908-c64db8f9ba71

import Definitions.Def_Eden_LyapunovExponents
import Mathlib.Data.Finset.Max
import Definitions.Def_Eden_KaplanYorke
import Theorems.Thm_Eden_spectrumPartialSum_succ
import Theorems.Thm_Eden_kaplanYorkeIndex_mem
import Theorems.Thm_Eden_spectrumPartialSum_after_index_neg

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {a : Fin 5 → ℝ}
    (hj : kaplanYorkeIndex a < 5) : spectrumEntry a (kaplanYorkeIndex a) < 0 := by
  have hsum := spectrumPartialSum_after_index_neg
    (show kaplanYorkeIndex a < kaplanYorkeIndex a + 1 by omega) (by omega)
  rw [spectrumPartialSum_succ] at hsum
  have := (kaplanYorkeIndex_mem a).2
  linarith
end Eden
