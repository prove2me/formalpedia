-- Prove2me | solution 1 for BSLambda.iterBlock_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:35:50.273082+00:00
-- url     : https://prove2.me/submissions/bbb47edb-121f-4066-9472-7204deaf10d9

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open Function
universe u
variable {V ι : Type*} [DecidableEq V] {blk : ι → Finset V}
namespace BSLambda
theorem _root_.solution (hne : ∀ i, (blk i).Nonempty) :
    ∀ (m : ℕ) (t : IterCoord ι m), (iterBlock blk m t).Nonempty
  | 0 => fun _ ↦ ⟨PUnit.unit, Finset.mem_univ (α := PUnit) _⟩
  | m + 1 => fun t ↦ (hne t.1).product (solution hne m t.2)
end BSLambda
