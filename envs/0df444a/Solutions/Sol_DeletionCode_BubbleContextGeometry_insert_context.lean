-- Prove2me | solution 1 for DeletionCode.BubbleContextGeometry.insert_context
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:37.767223+00:00
-- url     : https://prove2.me/submissions/ceaf5c1f-2967-4347-b251-30d326c0f752

import Definitions.Def_DeletionCode_BubbleEndpoints
import Definitions.Def_DeletionCode_BubblePathSimplicity
import Definitions.Def_DeletionCode_BubbleLocalSpectrum
import Definitions.Def_DeletionCode_BubbleContextGeometry
import Theorems.Thm_DeletionCode_BubbleContextGeometry_cut_bounds
import Theorems.Thm_DeletionCode_BubbleContextGeometry_delete_context
import Theorems.Thm_DeletionCode_SpectrumLocalization_listLetters_middle
import Theorems.Thm_DeletionCode_Windows_insert_delete


set_option autoImplicit true
open DeletionCode DeletionCode.BubbleContextGeometry
open Windows HeaderRecovery CatalogueWords SpectrumLocalization
namespace DeletionCode.BubbleContextGeometry
theorem _root_.solution {k : ℕ} (bubble : BubbleWord k) (x y : List Bool) :
    insertAt (listLetters (x ++ (bubble.shortWord ++ y)))
        (x.length + editOffset k) bubble.bit =
      listLetters (x ++ (bubble.longWord ++ y)) := by
  have hbit : listLetters (x ++ (bubble.longWord ++ y)) (x.length + editOffset k) =
      bubble.bit := by
    rw [listLetters_middle x bubble.longWord y _ (cut_bounds bubble).1]
    exact bubble.header_bit
  calc
    insertAt (listLetters (x ++ (bubble.shortWord ++ y)))
        (x.length + editOffset k) bubble.bit =
      insertAt (deleteAt (listLetters (x ++ (bubble.longWord ++ y)))
        (x.length + editOffset k)) (x.length + editOffset k)
        (listLetters (x ++ (bubble.longWord ++ y)) (x.length + editOffset k)) := by
          rw [delete_context, hbit]
    _ = _ := insert_delete _ _
end DeletionCode.BubbleContextGeometry
