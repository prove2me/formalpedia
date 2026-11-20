-- Prove2me | solution 1 for DeletionCode.WalkSelection.independent_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:13:47.543611+00:00
-- url     : https://prove2.me/submissions/ab0bf12e-702c-4388-9304-201b9332541d

import Definitions.Def_DeletionCode_ClosedWalk
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_DeletionCode_WalkSelection

set_option autoImplicit true
open DeletionCode DeletionCode.WalkSelection
open scoped BigOperators
variable {V : Type*} [AddCommGroup V] [Module ℚ V] {m : ℕ}
namespace DeletionCode.WalkSelection
theorem _root_.solution {step : Fin m → V} {S : Finset (Fin m)}
    (hs : LinearIndepOn ℚ step (S : Set (Fin m))) (i : Fin m)
    (hi : step i ∉ selectedSpan step S) :
    LinearIndepOn ℚ step ((insert i S : Finset (Fin m)) : Set (Fin m)) := by
  simpa only [Finset.coe_insert] using hs.insert hi
end DeletionCode.WalkSelection
