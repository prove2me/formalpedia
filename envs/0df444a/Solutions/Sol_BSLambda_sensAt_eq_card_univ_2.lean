-- Prove2me | solution 2 for BSLambda.sensAt_eq_card_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:55:02.972886+00:00
-- url     : https://prove2.me/submissions/f55d1656-dc8c-4204-8bd7-afd13ab75a7b

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BSLambda
theorem _root_.solution {f : Input V → Bool} {x : Input V} (h : ∀ v, SensitiveCoord f x v) :
    sensAt f x = Fintype.card V := by
  rw [sensAt, sensCoords, Finset.filter_true_of_mem fun v _ ↦ h v, Finset.card_univ]
end BSLambda
