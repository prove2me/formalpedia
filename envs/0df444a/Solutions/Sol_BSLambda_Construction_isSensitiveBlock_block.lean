-- Prove2me | solution 1 for BSLambda.Construction.isSensitiveBlock_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:23:39.222143+00:00
-- url     : https://prove2.me/submissions/ed962544-c7a4-402a-9d48-6171bbe9f258

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_BlockSens
public import Theorems.Thm_BSLambda_Construction_ind_zeroInput
public import Theorems.Thm_BSLambda_Construction_ind_flipSet_block
public import Theorems.Thm_BSLambda_Construction_block_nonempty
public import Theorems.Thm_BSLambda_isSensitiveBlock_of_eq_true


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Construction
variable {ι : Type*} {r : ℕ}
variable {Arc : ι → ι → Bool} {γ : ι → ι → Fin r}
namespace BSLambda.Construction
theorem _root_.solution [Fintype ι] [DecidableEq ι] [NeZero r] (i : ι) :
    IsSensitiveBlock (ind Arc γ) (zeroInput (Coord ι r)) (block i) :=
  isSensitiveBlock_of_eq_true (block_nonempty i) (ind_zeroInput Arc γ) (ind_flipSet_block i)
end BSLambda.Construction
