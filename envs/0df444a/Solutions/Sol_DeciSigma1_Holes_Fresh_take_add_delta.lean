-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.take_add_delta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:46:33.944593+00:00
-- url     : https://prove2.me/submissions/d1f81ced-dd01-465b-9aaf-7805bc0fdede

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}
variable {W : Fin k → List α}
omit [DecidableEq α]
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {x : List α} {c δ e : ℕ} (he : c ≤ e) :
    x.take (e + δ) = x.take (c + δ) ++ (x.drop (c + δ)).take (e - c) := by
  rw [← List.take_add]; congr 1; omega
end DeciSigma1.Holes.Fresh
