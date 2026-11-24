-- Prove2me | solution 1 for FairSelling.SEF1_SEFX_relaxation_of_EF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:51:42.031771+00:00
-- url     : https://prove2.me/submissions/9289773d-5591-4073-9a48-a1f9570de10a

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaTen
import Definitions.Def_RequestProject_EnvyRelaxation
import Theorems.Thm_FairSelling_SEF1_of_SEFX
import Theorems.Thm_FairSelling_SEFX_of_EF


set_option autoImplicit true
open scoped BigOperators
open FairSelling
namespace FairSelling
theorem _root_.solution {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (v : Fin n → G → ℝ) (p : G → ℝ) (o : Outcome G n) (hv : ∀ i g, 0 ≤ v i g)
    (hvalid : o.Valid p) (hEF : EF v p o) :
    SEFX v p o ∧ SEF1 v p o :=
  ⟨SEFX_of_EF hEF, SEF1_of_SEFX hv hvalid (SEFX_of_EF hEF)⟩
end FairSelling
