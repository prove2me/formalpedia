-- Prove2me | solution 1 for FairChores.MMS_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:19:55.612438+00:00
-- url     : https://prove2.me/submissions/3bffd0f4-856c-424c-9ace-e9522b13893b

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Theorems.Thm_FairChores_cost_nonneg
import Theorems.Thm_FairChores_MMSset_nonempty

set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ}
namespace FairChores
theorem _root_.solution (hc : ∀ t, 0 ≤ c t) (hn : 0 < n) : 0 ≤ MMS n c p :=
  le_csInf (MMSset_nonempty hc hn) (by
    rintro r ⟨o, hvalid, hle⟩
    exact le_trans (cost_nonneg hc hvalid ⟨0, hn⟩) (hle ⟨0, hn⟩))
end FairChores
