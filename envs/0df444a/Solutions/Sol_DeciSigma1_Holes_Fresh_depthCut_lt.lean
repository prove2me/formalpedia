-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.depthCut_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:46:20.474405+00:00
-- url     : https://prove2.me/submissions/040c5e74-af81-41ac-87a3-fa8151af80bb

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Mathlib.Order.Nat
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Theorems.Thm_DeciSigma1_Holes_Fresh_anchorCount_anti
public import Theorems.Thm_DeciSigma1_Holes_Fresh_depthCut_spec

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {W : Fin k → List α} {t : ℕ}
    {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t) {d : ℕ} (hd : d < lowerBlockCount W t o) :
    depthCut W t o (d + 1) < depthCut W t o d := by
  obtain ⟨hall, hlast⟩ := depthCut_spec ho
  obtain ⟨-, hs, -, hcnt⟩ := hall d hd
  by_cases h : d + 1 < lowerBlockCount W t o
  · obtain ⟨-, -, -, hcnt'⟩ := hall (d + 1) h
    by_contra hge
    have := anchorCount_anti (A := anchors W t o.1) (e := o.2.2) (not_lt.mp hge)
    omega
  · have hd' : d + 1 = lowerBlockCount W t o := by omega
    rw [hd', hlast]
    exact hs
end DeciSigma1.Holes.Fresh
