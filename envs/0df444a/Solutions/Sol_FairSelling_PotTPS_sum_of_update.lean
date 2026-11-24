-- Prove2me | solution 1 for FairSelling.PotTPS.sum_of_update
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:03:00.801834+00:00
-- url     : https://prove2.me/submissions/16a3d8e3-4ac4-4b51-8114-c236e92ff76d

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPot
import Definitions.Def_RequestProject_TPSSefxPotStep

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PotTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling.PotTPS
theorem _root_.solution {N : ℕ} (F F' : Fin N → ℝ) (k : Fin N) (h : ∀ i, i ≠ k → F' i = F i) :
    ∑ i, F' i = ∑ i, F i - F k + F' k := by
  classical
  rw [← Finset.add_sum_erase _ F' (Finset.mem_univ k),
      ← Finset.add_sum_erase _ F (Finset.mem_univ k)]
  have h2 : ∑ i ∈ Finset.univ.erase k, F' i = ∑ i ∈ Finset.univ.erase k, F i :=
    Finset.sum_congr rfl (fun i hi => h i (Finset.mem_erase.mp hi).1)
  rw [h2]; ring
end FairSelling.PotTPS
