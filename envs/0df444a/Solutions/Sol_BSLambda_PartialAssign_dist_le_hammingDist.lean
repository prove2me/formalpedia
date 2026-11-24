-- Prove2me | solution 1 for BSLambda.PartialAssign.dist_le_hammingDist
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:53:57.957975+00:00
-- url     : https://prove2.me/submissions/a8174151-2212-4fa5-8fd9-a4133a1af634

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


theorem solution {P : PartialAssign V} {x y : Input V} (hy : P.Sat y) :
    P.dist x ≤ hammingDist x y := by
  classical
  apply Finset.card_le_card
  intro v hv; simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  intro he
  have H : P v ≠ none ∧ P v ≠ some (x v) := by simpa [violSet] using hv
  cases e : P v with
  | none => exact H.1 e
  | some b => exact H.2 (by rw [e,he,hy v b e])
