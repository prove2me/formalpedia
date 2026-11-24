-- Prove2me | solution 1 for BSLambda.PartialAssign.Conflict.disjoint_cube
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:53:56.239021+00:00
-- url     : https://prove2.me/submissions/14d24ee4-6e60-4655-8112-1be3f55ea4d9

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.PartialAssign
variable {V : Type*}
variable [Fintype V] [DecidableEq V]


theorem solution {P Q : PartialAssign V} {v : V} (h : P.Conflict Q v) :
    Disjoint P.cube Q.cube := by
  apply Finset.disjoint_left.mpr
  intro x hp hq
  obtain ⟨b,eb,ec⟩ := h
  have hx : P.Sat x := by simpa [cube] using hp
  have hy : Q.Sat x := by simpa [cube] using hq
  have eq := (hx v b eb).symm.trans (hy v (!b) ec)
  cases b <;> simp at eq
