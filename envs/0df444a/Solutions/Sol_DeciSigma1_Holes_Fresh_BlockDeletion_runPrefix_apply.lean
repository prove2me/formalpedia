-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.BlockDeletion.runPrefix_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:33:17.740959+00:00
-- url     : https://prove2.me/submissions/01ba5f5f-1eb7-410b-a08d-19f2b7687b9c

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
public import Theorems.Thm_DeciSigma1_Holes_Fresh_runFrom_deleteSites
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
theorem _root_.solution (l : Fin k) (a : ℕ) :
    T.runPrefix m.apply l a =
      T.runPrefix W l (greatestPreimage (sitePositions m.deletionLength (m.sites l)) a) :=
  runFrom_deleteSites T (T.start l) (m.strictlySeparated l)
    (fun _ hc => ⟨(m.site_valid hc).2.1, (m.site_valid hc).2.2⟩) a
end DeciSigma1.Holes.Fresh.BlockDeletion
