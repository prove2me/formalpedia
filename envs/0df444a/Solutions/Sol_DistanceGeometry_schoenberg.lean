-- Prove2me | solution 1 for DistanceGeometry.schoenberg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:49:00.804844+00:00
-- url     : https://prove2.me/submissions/d53926f2-0c5e-481a-a5be-7807a5213098

module
public import Definitions.Def_LeanPool_DistanceGeometry_Defs
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Definitions.Def_LeanPool_DistanceGeometry_Schoenberg
public import Mathlib.Analysis.Matrix.PosDef
public import Definitions.Def_LeanPool_DistanceGeometry_SchoenbergHard
public import Theorems.Thm_DistanceGeometry_schoenberg_hard
public import Theorems.Thm_DistanceGeometry_schoenberg_easy


set_option autoImplicit true
@[expose] public section
public section
open Matrix
open scoped RealInnerProductSpace
open DistanceGeometry
open Matrix
open scoped RealInnerProductSpace
variable {n k : ℕ} [NeZero n]
namespace DistanceGeometry
theorem _root_.solution {D : Matrix (Fin n) (Fin n) ℝ} (hD : IsPreDistMatrix D) :
    EmbedsIn D k ↔ (centeredGram D).PosSemidef ∧ (centeredGram D).rank ≤ k := by
  constructor
  · rintro ⟨x, hx⟩
    exact schoenberg_easy hx
  · rintro ⟨hPSD, hrank⟩
    exact schoenberg_hard hD hPSD hrank
end DistanceGeometry
