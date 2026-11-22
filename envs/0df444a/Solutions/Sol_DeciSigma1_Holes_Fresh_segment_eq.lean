-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.segment_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:47:53.892745+00:00
-- url     : https://prove2.me/submissions/f11a4925-4ef3-47d7-a74d-969273016365

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}
omit [DecidableEq α]
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {x z : List α} {p n r r' : ℕ} (hz : (x.drop p).take n = z) (h1 : r' ≤ r)
    (h2 : r ≤ n) : (x.drop (p + r')).take (r - r') = (z.drop r').take (r - r') := by
  rw [← hz, List.drop_take, ← List.drop_drop, List.take_take, Nat.min_eq_left (by omega)]
end DeciSigma1.Holes.Fresh
