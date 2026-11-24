-- Prove2me | solution 1 for FongoSync.order_matters_without_unique_clocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:03:40.129308+00:00
-- url     : https://prove2.me/submissions/24c5c968-dcfe-4c5a-9503-6751f0c8f65a

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Examples

set_option autoImplicit false
open FongoSync
namespace FongoSync
theorem _root_.solution :
    let σ : String → String → Strategy := fun _ _ => .lww
    let a : Change Value := ⟨"things", 0, "title", .int 1, ⟨1, 0, 1⟩⟩
    let b : Change Value := ⟨"things", 0, "title", .int 2, ⟨1, 0, 1⟩⟩
    merged σ [a, b] ("things", 0, "title") ≠ merged σ [b, a] ("things", 0, "title") := by
  decide
end FongoSync
