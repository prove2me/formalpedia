-- Prove2me | solution 1 for FairSelling.theorem_two_SEFX
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:04:00.353463+00:00
-- url     : https://prove2.me/submissions/046f4f6c-193e-4dcb-8a21-caea5b46340e

import Mathlib
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPhaseImp
import Definitions.Def_RequestProject_TPSSefxPotImp
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSSefxTheorem2
import Theorems.Thm_FairSelling_PotTPS_exists_TPS_SEFX_of_Qstep
import Theorems.Thm_FairSelling_PotTPS_qimprovementStep


set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) :
    ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, ((n : ℝ) / (2 * n - 1)) * TPS n (v i) p ≤ util (v i) o i) ∧ SEFX v p o :=
  PotTPS.exists_TPS_SEFX_of_Qstep v p hn hp
    (fun eps heps => PotTPS.qimprovementStep v p eps hn hp heps.le)
end FairSelling
