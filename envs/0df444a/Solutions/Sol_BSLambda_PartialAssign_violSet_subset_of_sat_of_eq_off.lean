-- Prove2me | solution 1 for BSLambda.PartialAssign.violSet_subset_of_sat_of_eq_off
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:50:29.672299+00:00
-- url     : https://prove2.me/submissions/1cca756b-6207-4fd3-9129-51adcb050e7e

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.PartialAssign
variable {V : Type*}
variable [Fintype V]


theorem solution {P : PartialAssign V} {x y : Input V} {A : Finset V}
    (hx : P.Sat x) (h : ∀ v ∉ A, y v = x v) : P.violSet y ⊆ A := by
  intro v hv
  by_contra hvA
  have H : P v ≠ none ∧ P v ≠ some (y v) := by simpa [violSet] using hv
  cases e : P v with
  | none => exact H.1 e
  | some b => exact H.2 (by rw [e, h v hvA, hx v b e])
