-- Prove2me | solution 1 for Erdos180.subdivisionLine_centers_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:47:33.22542+00:00
-- url     : https://prove2.me/submissions/f1316189-48e5-4083-a3f6-48916682dec7

import Definitions.Def_erdos180_core4
import Mathlib.Algebra.Field.Defs
import Mathlib.Combinatorics.SimpleGraph.Copy

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem solution
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    (C : Fin k → SymplecticLine K)
    (hcenter : ∀ center : Fin k,
      copy (.inl (.inr center)) = .inr (C center)) :
    Function.Injective C := by
  intro i j hij
  apply Sum.inr.inj
  apply Sum.inl.inj
  apply copy.injective
  change copy (.inl (.inr i)) = copy (.inl (.inr j))
  rw [hcenter i, hcenter j, hij]
