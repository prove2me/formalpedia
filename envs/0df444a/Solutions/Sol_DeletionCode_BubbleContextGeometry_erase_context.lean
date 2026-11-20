-- Prove2me | solution 1 for DeletionCode.BubbleContextGeometry.erase_context
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:28.559282+00:00
-- url     : https://prove2.me/submissions/dc80f9fe-39d1-4d78-a772-359d7689aa8a

import Definitions.Def_DeletionCode_BubbleEndpoints
import Definitions.Def_DeletionCode_BubblePathSimplicity
import Definitions.Def_DeletionCode_BubbleLocalSpectrum
import Definitions.Def_DeletionCode_BubbleContextGeometry
import Theorems.Thm_DeletionCode_BubbleContextGeometry_cut_bounds
import Theorems.Thm_DeletionCode_CatalogueWords_BubbleWord_eraseIdx_longWord


set_option autoImplicit true
open DeletionCode DeletionCode.BubbleContextGeometry
open Windows HeaderRecovery CatalogueWords SpectrumLocalization
namespace DeletionCode.BubbleContextGeometry
theorem _root_.solution {k : ℕ} (bubble : BubbleWord k) (x y : List Bool) :
    (x ++ (bubble.longWord ++ y)).eraseIdx (x.length + editOffset k) =
      x ++ (bubble.shortWord ++ y) := by
  rw [List.eraseIdx_append_of_length_le (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.eraseIdx_append_of_lt_length (cut_bounds bubble).1, bubble.eraseIdx_longWord]
end DeletionCode.BubbleContextGeometry
