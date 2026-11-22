-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.runFrom_deleteSites
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:27:10.756342+00:00
-- url     : https://prove2.me/submissions/b128ec51-274a-485a-be85-8199fa2317d2

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_sitePositions
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_sites_of_maximal_interval
public import Theorems.Thm_DeciSigma1_Words_runFrom_take_deletePositions


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}
variable {W : Fin k → List α}
variable {δ : ℕ} {cs : Finset ℕ}
variable {S : Type}
omit [DecidableEq α]
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution (T : Table α S k) (q0 : S) {x : List α} (hs : StrictlySeparated δ cs)
    (hst : ∀ c ∈ cs, c + δ < x.length ∧
      runFrom T.step q0 (x.take c) = runFrom T.step q0 (x.take (c + δ)))
    (a : ℕ) :
    runFrom T.step q0 ((deletePositions x (sitePositions δ cs)).take a) =
      runFrom T.step q0 (x.take (greatestPreimage (sitePositions δ cs) a)) := by
  refine runFrom_take_deletePositions T q0 x (fun j c hjc _ hD hj hc => ?_) (fun h => ?_) a
  · obtain ⟨hjs, rfl⟩ := mem_sites_of_maximal_interval hs hjc hD hj hc
    exact (hst j hjs).2
  · obtain ⟨c, hc, h1, h2⟩ := mem_sitePositions.mp h
    have := (hst c hc).1; omega
end DeciSigma1.Holes.Fresh
