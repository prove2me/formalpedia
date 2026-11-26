-- Prove2me | solution 1 for Eden.spectrumInterpolation_index_criterion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:09:29.824915+00:00
-- url     : https://prove2.me/submissions/d9b87b5b-e13e-4d8c-a83b-1002faeaadf0

import Definitions.Def_Eden_LogarithmicInterpolation
import Definitions.Def_Eden_InterpolationSign
import Theorems.Thm_Eden_kaplanYorkeDimension_formula_of_index_lt_five
import Theorems.Thm_Eden_spectrumEntry_at_kaplanYorkeIndex_neg


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {a : Fin 5 → ℝ}
    (hj : kaplanYorkeIndex a < 5) (α : ℝ) :
    0 ≤ spectrumPartialSum a (kaplanYorkeIndex a) + α * spectrumEntry a (kaplanYorkeIndex a) ↔
      (kaplanYorkeIndex a : ℝ) + α ≤ kaplanYorkeDimension a := by
  rw [kaplanYorkeDimension_formula_of_index_lt_five hj, add_le_add_iff_left,
    le_div_iff₀ (show 0 < -spectrumEntry a (kaplanYorkeIndex a) from
      neg_pos.mpr (spectrumEntry_at_kaplanYorkeIndex_neg hj))]
  constructor <;> intro h <;> nlinarith
end Eden
