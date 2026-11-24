-- Prove2me | solution 1 for FongoSync.Laws.view_set
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:09:18.006708+00:00
-- url     : https://prove2.me/submissions/a6ed8fe7-5b4a-448a-8aef-f1e3ff5b3da5

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
import Theorems.Thm_FongoSync_Full_view_eq_of_mem_iff
import Theorems.Thm_FongoSync_IsCanonical_unique
import Theorems.Thm_FongoSync_view_eq_of_mem_iff


set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync
namespace FongoSync.Laws
theorem _root_.solution (sc : Schema) {cs₁ cs₂ : List (Change Value)}
    (same : ∀ c, c ∈ cs₁ ↔ c ∈ cs₂) (unique : ClockDetermines cs₁) :
    view sc cs₁ = view sc cs₂ :=
  view_eq_of_mem_iff sc same unique
end FongoSync.Laws
