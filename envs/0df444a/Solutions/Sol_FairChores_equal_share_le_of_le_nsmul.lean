-- Prove2me | solution 1 for FairChores.equal_share_le_of_le_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:23:41.303737+00:00
-- url     : https://prove2.me/submissions/acc34efd-5040-4324-963d-e69578b47463

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresPreAlloc
import Definitions.Def_RequestProject_ChoresBagLemma
import Definitions.Def_RequestProject_ChoresBagFilling

set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
variable {c : Fin n → T → ℝ} {p : T → ℝ} {mu : Fin n → ℝ}
namespace FairChores
theorem _root_.solution {W m : ℝ} {k : ℕ} (hk : 1 ≤ k) (hW : W ≤ k * m) :
    W / k ≤ m := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  rw [div_le_iff₀ hk0]
  linarith [hW]
end FairChores
