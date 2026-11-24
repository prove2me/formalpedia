-- Prove2me | solution 1 for FongoSync.Laws.groups_set
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:09:00.307869+00:00
-- url     : https://prove2.me/submissions/df62e9d4-92d7-4414-9d09-b917d911b5da

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
import Theorems.Thm_FongoSync_canonical_eq_of_mem_iff


set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync
namespace FongoSync.Laws
theorem _root_.solution (E₁ E₂ : List Edge) (same : ∀ e, e ∈ E₁ ↔ e ∈ E₂) :
    canonical E₁ = canonical E₂ :=
  canonical_eq_of_mem_iff E₁ E₂ same
end FongoSync.Laws
