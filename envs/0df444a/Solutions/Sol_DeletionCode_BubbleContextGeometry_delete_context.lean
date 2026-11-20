-- Prove2me | solution 1 for DeletionCode.BubbleContextGeometry.delete_context
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:38.545777+00:00
-- url     : https://prove2.me/submissions/da876ad8-53de-4c5a-aa83-107e56dc1db2

import Definitions.Def_DeletionCode_BubbleEndpoints
import Definitions.Def_DeletionCode_BubblePathSimplicity
import Definitions.Def_DeletionCode_BubbleLocalSpectrum
import Definitions.Def_DeletionCode_BubbleContextGeometry
import Theorems.Thm_DeletionCode_BubbleContextGeometry_erase_context
import Theorems.Thm_DeletionCode_CatalogueWords_listLetters_eraseIdx


set_option autoImplicit true
open DeletionCode DeletionCode.BubbleContextGeometry
open Windows HeaderRecovery CatalogueWords SpectrumLocalization
namespace DeletionCode.BubbleContextGeometry
theorem _root_.solution {k : ℕ} (bubble : BubbleWord k) (x y : List Bool) :
    deleteAt (listLetters (x ++ (bubble.longWord ++ y))) (x.length + editOffset k) =
      listLetters (x ++ (bubble.shortWord ++ y)) := by
  rw [← listLetters_eraseIdx, erase_context]
end DeletionCode.BubbleContextGeometry
