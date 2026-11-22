-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.drop_eq_take_append_site
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:47:48.116933+00:00
-- url     : https://prove2.me/submissions/d0fd06ae-d89d-48c9-b9d7-ef35cc334fb8

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} {δ : ℕ}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {x : List α} {F : List α} {p d c : ℕ} (hpc : p + d = c)
    (hF : (x.drop c).take δ = F) :
    x.drop p = (x.drop p).take d ++ (F ++ x.drop (c + δ)) := by
  rw [← hF, ← List.drop_drop, List.take_append_drop, ← hpc, ← List.drop_drop,
    List.take_append_drop]
end DeciSigma1.Holes.Fresh
