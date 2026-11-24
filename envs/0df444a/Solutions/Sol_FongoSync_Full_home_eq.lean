-- Prove2me | solution 1 for FongoSync.Full.home_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:03:20.586815+00:00
-- url     : https://prove2.me/submissions/1f47b1ec-405c-4eca-a359-8dacda61d667

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Model
import Theorems.Thm_FongoSync_fold_keep_eq_of_mem_iff


set_option autoImplicit false
open FongoSync FongoSync.Full
open Std Classical FongoSync
set_option linter.unusedSectionVars false
variable (sc : Full.Schema) {cs₁ cs₂ : List (Change Value)} (same : ∀ c, c ∈ cs₁ ↔ c ∈ cs₂)
include same
namespace FongoSync.Full
theorem _root_.solution : home sc cs₁ = home sc cs₂ := by
  funext g
  simp only [home]
  congr 1
  exact fold_keep_eq_of_mem_iff (cmp := claimFirst) (key := id) _ _ (fun x => by
    simp only [List.mem_map, List.mem_filter, same])
    (fun a _ b _ h => h)
end FongoSync.Full
