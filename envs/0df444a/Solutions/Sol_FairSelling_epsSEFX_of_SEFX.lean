-- Prove2me | solution 1 for FairSelling.epsSEFX_of_SEFX
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:38:59.120587+00:00
-- url     : https://prove2.me/submissions/d63a645f-3909-407f-98a1-7a960be86723

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Theorems.Thm_FairSelling_epsSEFX_zero_iff
import Theorems.Thm_FairSelling_epsSEFX_mono

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [DecidableEq G] {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}
namespace FairSelling
theorem _root_.solution {eps : ℝ} (heps : 0 ≤ eps) (ho : SEFX v p o) : epsSEFX v p eps o :=
  epsSEFX_mono heps (epsSEFX_zero_iff.2 ho)
end FairSelling
