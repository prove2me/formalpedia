-- Prove2me | solution 1 for DeletionCode.EditAlignment.Alignment.from_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:15:44.638738+00:00
-- url     : https://prove2.me/submissions/362853c1-6750-420e-9c59-1ff6d1ed3709

import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_EditAlignment

set_option autoImplicit true
open DeletionCode DeletionCode.EditAlignment
namespace DeletionCode.EditAlignment
namespace Alignment
theorem _root_.solution (z : Word) : Alignment [] z 0 z.length := by
  induction z with
  | nil => exact Alignment.nil
  | cons bit tail ih => exact Alignment.insertion bit ih
end Alignment
end DeletionCode.EditAlignment
