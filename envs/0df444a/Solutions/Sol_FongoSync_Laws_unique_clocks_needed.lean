-- Prove2me | solution 1 for FongoSync.Laws.unique_clocks_needed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:08:39.975847+00:00
-- url     : https://prove2.me/submissions/72a54c63-3469-45dd-900e-b3056e35d788

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
import Theorems.Thm_FongoSync_order_matters_without_unique_clocks


set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync
namespace FongoSync.Laws
theorem _root_.solution :
    let σ : String → String → Strategy := fun _ _ => .lww
    let a : Change Value := ⟨"things", 0, "title", .int 1, ⟨1, 0, 1⟩⟩
    let b : Change Value := ⟨"things", 0, "title", .int 2, ⟨1, 0, 1⟩⟩
    merged σ [a, b] ("things", 0, "title") ≠ merged σ [b, a] ("things", 0, "title") :=
  order_matters_without_unique_clocks
end FongoSync.Laws
