-- Prove2me | solution 1 for BSLambda.Construction.ind_flipSet_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:12:56.384794+00:00
-- url     : https://prove2.me/submissions/68e67097-1b9b-4d1d-8599-c001bf1302b9

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_BlockSens
public import Theorems.Thm_BSLambda_Construction_sat_cert_flipSet_block
public import Theorems.Thm_BSLambda_Construction_ind_eq_true_of_sat


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Construction
variable {ι : Type*} {r : ℕ}
variable {Arc : ι → ι → Bool} {γ : ι → ι → Fin r}
namespace BSLambda.Construction
theorem _root_.solution [Fintype ι] [DecidableEq ι] (i : ι) :
    ind Arc γ (flipSet (zeroInput (Coord ι r)) (block i)) = true :=
  ind_eq_true_of_sat (sat_cert_flipSet_block i)
end BSLambda.Construction
