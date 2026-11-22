-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.ne_nil_of_mem_upperOccurrences
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:53:20.755871+00:00
-- url     : https://prove2.me/submissions/3e7fa493-f966-493f-9ce2-135e5825658d

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Mathlib.Order.Nat
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_upperOcc

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {W : Fin k → List α} {t : ℕ} {o : Fin k × ℕ × ℕ}
    (ho : o ∈ upperOccurrences W t) : W o.1 ≠ [] := (mem_upperOcc.mp ho).1
end DeciSigma1.Holes.Fresh
