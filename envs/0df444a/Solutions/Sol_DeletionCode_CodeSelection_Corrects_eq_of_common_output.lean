-- Prove2me | solution 1 for DeletionCode.CodeSelection.Corrects.eq_of_common_output
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:44:06.506732+00:00
-- url     : https://prove2.me/submissions/93ad9fce-06ab-4673-825a-f92ede48793a

import Definitions.Def_DeletionCode_BipartiteSelection
import Definitions.Def_DeletionCode_ConflictGraphWitness
import Definitions.Def_DeletionCode_CodeSelection

set_option autoImplicit true
open DeletionCode DeletionCode.CodeSelection
open HeaderRecovery ConflictGraphWitness BipartiteSelection
variable {n k : ℕ}
namespace DeletionCode.CodeSelection
namespace Corrects
theorem _root_.solution {t : ℕ} {C : Finset (Bits n)} (hC : Corrects t C)
    {x y : Bits n} (hx : x ∈ C) (hy : y ∈ C) (output : List Bool)
    (hxo : EditAlignment.WithinEdits t (List.ofFn x) output)
    (hyo : EditAlignment.WithinEdits t (List.ofFn y) output) : x = y := by
  by_contra hxy
  exact hC x hx y hy hxy ⟨output, hxo, hyo⟩
end Corrects
end DeletionCode.CodeSelection
