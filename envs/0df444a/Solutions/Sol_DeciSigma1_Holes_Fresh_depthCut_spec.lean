-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.depthCut_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:45:43.619541+00:00
-- url     : https://prove2.me/submissions/42a33e48-51cb-4f12-bde4-2b317e543337

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Mathlib.Order.Nat
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Theorems.Thm_DeciSigma1_Holes_Fresh_depthCutAt_spec
public import Theorems.Thm_DeciSigma1_Holes_Fresh_upperOcc_spec

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {W : Fin k → List α} {t : ℕ}
    {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t) :
    (∀ d < lowerBlockCount W t o, depthCut W t o d ∈ anchors W t o.1 ∧ o.2.1 < depthCut W t o d ∧
      depthCut W t o d ≤ o.2.2 ∧ anchorCount (anchors W t o.1) (depthCut W t o d) o.2.2 = d) ∧
      depthCut W t o (lowerBlockCount W t o) = o.2.1 := by
  obtain ⟨hse, -, he, hs, -⟩ := upperOcc_spec ho
  exact depthCutAt_spec hse he hs
end DeciSigma1.Holes.Fresh
