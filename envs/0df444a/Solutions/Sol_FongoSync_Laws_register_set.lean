-- Prove2me | solution 1 for FongoSync.Laws.register_set
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:08:20.645632+00:00
-- url     : https://prove2.me/submissions/e0deaf68-7ce9-4ee4-b3ef-17075a89ff72

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
import Theorems.Thm_FongoSync_IsCanonical_unique
import Theorems.Thm_FongoSync_fold_apply_eq_of_mem_iff


set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync
variable {V : Type} [Ord V] [Std.TransOrd V] [Std.LawfulEqOrd V]
namespace FongoSync.Laws
theorem _root_.solution (s : Strategy) (l₁ l₂ : List (Entry V)) (same : ∀ x, x ∈ l₁ ↔ x ∈ l₂)
    (unique : UniqueClocks l₁) :
    l₁.foldl (apply s) none = l₂.foldl (apply s) none :=
  fold_apply_eq_of_mem_iff s l₁ l₂ same unique
end FongoSync.Laws
