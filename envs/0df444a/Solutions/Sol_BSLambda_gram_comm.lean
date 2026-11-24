-- Prove2me | solution 1 for BSLambda.gram_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:21:57.958062+00:00
-- url     : https://prove2.me/submissions/fb7078e8-27d1-442e-9907-c1f1526746ef

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Spectral
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_SchurTest
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Bipartite
public import Theorems.Thm_BSLambda_gram_apply

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix Matrix.Norms.L2Operator
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BSLambda
theorem _root_.solution {f : Input V → Bool} (x y : Ones f) : gram f x y = gram f y x := by
  rw [gram_apply, gram_apply]
  exact congrArg _ (congrArg Finset.card (Finset.filter_congr fun _ _ ↦ and_comm))
end BSLambda
