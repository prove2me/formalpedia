-- Prove2me | solution 1 for FongoSync.Laws.full_view_set
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:09:20.871918+00:00
-- url     : https://prove2.me/submissions/9677473a-59d0-40a4-bedd-1fd40b41152d

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
theorem _root_.solution (sc : Full.Schema) {cs₁ cs₂ : List (Change Value)}
    (same : ∀ c, c ∈ cs₁ ↔ c ∈ cs₂) (unique : ClockDetermines cs₁) :
    Full.view sc cs₁ = Full.view sc cs₂ :=
  Full.view_eq_of_mem_iff sc same unique
end FongoSync.Laws
