-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.visits_le_visBound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:37:35.888249+00:00
-- url     : https://prove2.me/submissions/d502ccde-cfae-4d73-ab2c-a6e0fd6bceb0

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Construction
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000
import Theorems.Thm_EditMulticoloring_Dev_Ram_visits_length_le

section
-- module Solutions.EditMulticoloring.RamColor4
/-!
# `colorsAll`: the colour of `x` and of each of its neighbours (q379, Part G)

`colorsAll q t cfg1 cfg2 g X2 XA DG CLA`: `colorOf` (block `g .. g+50`, enumerator `cfg2`) on `x`
(result `g+51`), then the enumerator `cfg1` over `visits (2t) x`; for every visited `w` of length
`|x|` other than `x` (in visit order, duplicates kept: the list `nbrList t x`) it copies `w`
into `cfg2.buf (2t)`, runs `colorOf` and stores the colour at `CLA[J]`, `J := J + 1` (`g+52`).
Own registers `g+51 .. g+67`; `cfg2.r0 ≥ g + 68`, `cfg1.r0` above the registers of `cfg2`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

theorem visits_le_visBound_oai {q : ℕ} (t : ℕ) (w : Word q) :
    (visits (2 * t) w).length ≤ visBound q t w.length := visits_length_le (2 * t) w

/-! ## The program -/

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.visits_le_visBound_oai := @EditMulticoloring.Dev.Ram.visits_le_visBound_oai
