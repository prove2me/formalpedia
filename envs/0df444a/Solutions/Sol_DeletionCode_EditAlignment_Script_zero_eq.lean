-- Prove2me | solution 1 for DeletionCode.EditAlignment.Script.zero_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:16.91137+00:00
-- url     : https://prove2.me/submissions/d6b746ac-c8fc-4c4b-92b4-83e7636b7f97

import Definitions.Def_DeletionCode_EditAlignment
import Definitions.Def_DeletionCode_SingleEditOrigins
import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SingleEditScripts

set_option autoImplicit true
open DeletionCode DeletionCode.EditAlignment
namespace DeletionCode.EditAlignment
namespace Script
theorem _root_.solution {x y : Word} (h : Script x y 0 0) : x = y := by
  cases h
  rfl
end Script
end DeletionCode.EditAlignment
