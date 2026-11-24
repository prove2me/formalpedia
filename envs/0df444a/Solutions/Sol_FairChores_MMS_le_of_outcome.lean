-- Prove2me | solution 1 for FairChores.MMS_le_of_outcome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:19:26.149773+00:00
-- url     : https://prove2.me/submissions/a0a33a26-a600-4b86-ada2-a6b92135151b

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresMMSPartition
import Theorems.Thm_FairChores_MMSset_bddBelow


set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
namespace FairChores
theorem _root_.solution {c p : T → ℝ} (hc : ∀ t, 0 ≤ c t) (hn : 0 < n) {o : Outcome T n}
    (hvalid : o.Valid p) {r : ℝ} (hle : ∀ j, cost c o j ≤ r) : MMS n c p ≤ r :=
  csInf_le (MMSset_bddBelow hc hn) ⟨o, hvalid, hle⟩
end FairChores
