-- Prove2me | solution 1 for Eden.kaplanYorkeDimension_between_index
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:52:00.665083+00:00
-- url     : https://prove2.me/submissions/cd1200f3-9160-4189-81b9-fae136806da6

import Definitions.Def_Eden_LyapunovExponents
import Mathlib.Data.Finset.Max
import Definitions.Def_Eden_KaplanYorke
import Theorems.Thm_Eden_spectrumPartialSum_succ
import Theorems.Thm_Eden_kaplanYorkeIndex_mem
import Theorems.Thm_Eden_spectrumPartialSum_after_index_neg
import Theorems.Thm_Eden_spectrumEntry_at_kaplanYorkeIndex_neg
import Theorems.Thm_Eden_kaplanYorkeDimension_of_index_between

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {a : Fin 5 → ℝ}
    (hj₀ : 0 < kaplanYorkeIndex a) (hj₅ : kaplanYorkeIndex a < 5) :
    (kaplanYorkeIndex a : ℝ) ≤ kaplanYorkeDimension a ∧
      kaplanYorkeDimension a < (kaplanYorkeIndex a : ℝ) + 1 := by
  have hneg := spectrumEntry_at_kaplanYorkeIndex_neg hj₅
  have hsum := spectrumPartialSum_after_index_neg
    (show kaplanYorkeIndex a < kaplanYorkeIndex a + 1 by omega) (by omega)
  rw [spectrumPartialSum_succ] at hsum
  rw [kaplanYorkeDimension_of_index_between rfl hj₀ hj₅, abs_of_neg hneg]
  have hlo : 0 ≤ spectrumPartialSum a (kaplanYorkeIndex a) /
      -spectrumEntry a (kaplanYorkeIndex a) :=
    div_nonneg (kaplanYorkeIndex_mem a).2 (by linarith)
  have hhi : spectrumPartialSum a (kaplanYorkeIndex a) /
      -spectrumEntry a (kaplanYorkeIndex a) < 1 :=
    (div_lt_one (show 0 < -spectrumEntry a (kaplanYorkeIndex a) by linarith)).mpr
      (by linarith)
  constructor <;> linarith
end Eden
