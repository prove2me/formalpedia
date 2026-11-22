-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.BlockDeletion.contextAnchors_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:33:44.405826+00:00
-- url     : https://prove2.me/submissions/16a3be67-d86b-4d5a-88be-7256bba723d9

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
public import Theorems.Thm_DeciSigma1_Holes_Fresh_contextAnchors_deleteSites
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_strictlySeparated
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_site_valid

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}
variable {S : Type} [Fintype S]
open DeciSigma1.Holes.Fresh.BlockDeletion
variable {T : Table α S k} {W : Fin k → List α} {t : ℕ} (m : BlockDeletion T W t)
namespace DeciSigma1.Holes.Fresh.BlockDeletion
theorem _root_.solution {r : ℕ} (hr1 : 1 ≤ r) (hr : r ≤ t + 1) (l : Fin k) (e' : ℕ) :
    e' ∈ contextAnchors W r (m.apply l) ↔
      ∃ p ∈ contextAnchors W r (W l), Retained m.deletionLength (m.sites l) p ∧
        retainedCount (sitePositions m.deletionLength (m.sites l)) p = e' :=
  contextAnchors_deleteSites hr1 hr _ (m.strictlySeparated l)
    (fun _ hc => (m.site_valid hc).1) e'
end DeciSigma1.Holes.Fresh.BlockDeletion
