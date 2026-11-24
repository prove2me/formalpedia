-- Prove2me | solution 1 for FairChores.equal_share_le_three_halves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:23:52.098918+00:00
-- url     : https://prove2.me/submissions/5759e41c-7be0-4009-a82f-e094d2b326e9

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
theorem _root_.solution {W m : ℝ} {k : ℕ} (hk : 2 ≤ k) (hm : 0 ≤ m)
    (hW : W ≤ (k + 1) * m) : W / k ≤ 3 / 2 * m := by
  have hk0 : (0:ℝ) < k := by positivity
  have hk2 : (2:ℝ) ≤ k := by exact_mod_cast hk
  rw [div_le_iff₀ hk0]
  nlinarith
end FairChores
