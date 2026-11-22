-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.ValidDeletionSite.of_take
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:46:24.132816+00:00
-- url     : https://prove2.me/submissions/9cf27341-0fa0-486a-8b6a-c887fa109507

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
namespace DeciSigma1.Holes.Fresh
namespace ValidDeletionSite
theorem _root_.solution {t : ℕ} {x x' : List α} {c δ p : ℕ}
    (h : ValidDeletionSite W t x c δ)
    (hx : x'.take p = x.take p) (hp : c + δ ≤ p) (hlen : c + δ ≤ x'.length) :
    ValidDeletionSite W t x' c δ := by
  have e1 : x'.take c = x.take c := by
    rw [show c = min c p by omega, ← List.take_take, hx, List.take_take]
  have e2 : x'.take (c + δ) = x.take (c + δ) := by
    rw [show c + δ = min (c + δ) p by omega, ← List.take_take, hx, List.take_take]
  exact ⟨hlen, by rw [e1]; exact h.anchor, by rw [e1, e2]; exact h.types,
    by rw [e2]; exact h.no_upper_marker⟩
end ValidDeletionSite
end DeciSigma1.Holes.Fresh
