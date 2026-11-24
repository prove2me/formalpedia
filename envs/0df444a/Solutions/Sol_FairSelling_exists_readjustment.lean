-- Prove2me | solution 1 for FairSelling.exists_readjustment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:11:43.749498+00:00
-- url     : https://prove2.me/submissions/e850fd46-9093-476d-bbaf-4caa3e2a83a8

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_EquiMMS
import Theorems.Thm_FairSelling_exists_equiMMS

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g) :
    ∃ v' : Fin n → G → ℝ, (∀ i g, 0 ≤ v' i g) ∧ (∀ i g, v' i g ≤ v i g) ∧
      (∀ i, MMS n (v' i) p = MMS n (v i) p) ∧
      ∀ i, Nonempty (EquiMMS (v' i) p (MMS n (v' i) p) n) := by
  classical
  choose w hw0 hwv hwMMS hwE using fun i => exists_equiMMS hn (v i) p (hv i) hp
  exact ⟨w, hw0, hwv, hwMMS, hwE⟩
end FairSelling
