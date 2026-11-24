-- Prove2me | solution 1 for FongoSync.Laws.state_set
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:08:39.491832+00:00
-- url     : https://prove2.me/submissions/f23b93bb-5bdf-45c5-b5c8-d0be880f86a8

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
import Theorems.Thm_FongoSync_IsCanonical_unique
import Theorems.Thm_FongoSync_merged_eq_of_mem_iff


set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync
variable {V : Type} [Ord V] [Std.TransOrd V] [Std.LawfulEqOrd V]
namespace FongoSync.Laws
theorem _root_.solution (σ : String → String → Strategy) (cs₁ cs₂ : List (Change V))
    (same : ∀ c, c ∈ cs₁ ↔ c ∈ cs₂) (unique : ClockDetermines cs₁) :
    merged σ cs₁ = merged σ cs₂ :=
  merged_eq_of_mem_iff σ cs₁ cs₂ same unique
end FongoSync.Laws
