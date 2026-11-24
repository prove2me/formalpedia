-- Prove2me | solution 1 for FongoSync.Full.groupedAt_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:06:34.768841+00:00
-- url     : https://prove2.me/submissions/6d591414-b6a7-4e9a-8f9f-f532b6f1959f

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Model
import Theorems.Thm_FongoSync_Full_home_eq
import Theorems.Thm_FongoSync_Full_homeCollection_eq
import Theorems.Thm_FongoSync_Full_unverified_eq
import Theorems.Thm_FongoSync_Full_mem_edges_iff
import Theorems.Thm_FongoSync_Full_registers_eq
import Theorems.Thm_FongoSync_IsCanonical_unique


set_option autoImplicit false
open FongoSync FongoSync.Full
open Std Classical FongoSync
set_option linter.unusedSectionVars false
variable (sc : Full.Schema) {cs₁ cs₂ : List (Change Value)} (same : ∀ c, c ∈ cs₁ ↔ c ∈ cs₂)
include same
namespace FongoSync.Full
theorem _root_.solution (unique : ClockDetermines cs₁) (k : Nat) :
    groupedAt sc cs₁ k = groupedAt sc cs₂ k := by
  have he : (fun a b => (a, b) ∈ edges sc cs₁) = (fun a b => (a, b) ∈ edges sc cs₂) := by
    funext a b; exact propext (mem_edges_iff sc same _)
  have hk : KeyPair sc cs₁ = KeyPair sc cs₂ := by
    funext R a b
    simp only [KeyPair, homeCollection_eq sc same, home_eq sc same, unverified_eq sc same,
      registers_eq sc same unique]
  induction k with
  | zero => simp only [groupedAt, he]
  | succ k ih =>
    simp only [groupedAt, ih, hk]
    congr
    funext a b
    rw [propext (mem_edges_iff sc same (a, b))]
end FongoSync.Full
