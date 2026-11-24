-- Prove2me | solution 1 for FairChores.LitCounterexample.lit_not_relaxation_of_EF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:54:08.574246+00:00
-- url     : https://prove2.me/submissions/2dfe6f2e-5aa9-4cb4-b050-1608a9061813

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresEnvy
import Theorems.Thm_FairChores_LitCounterexample_oo_valid
import Theorems.Thm_FairChores_LitCounterexample_oo_EF
import Theorems.Thm_FairChores_LitCounterexample_oo_not_SEFXlit
import Theorems.Thm_FairChores_LitCounterexample_oo_not_SEF1lit

set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
open FairChores.LitCounterexample
namespace FairChores.LitCounterexample
theorem _root_.solution :
    ∃ (c : Fin 2 → Fin 2 → ℝ) (p : Fin 2 → ℝ) (o : Outcome (Fin 2) 2),
      o.Valid p ∧ EF c p o ∧ ¬ SEF1lit c p o ∧ ¬ SEFXlit c p o :=
  ⟨cc, pp, oo, oo_valid, oo_EF, oo_not_SEF1lit, oo_not_SEFXlit⟩
end FairChores.LitCounterexample
