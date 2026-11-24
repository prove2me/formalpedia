-- Prove2me | solution 1 for FairSelling.losses_initial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:10:19.963899+00:00
-- url     : https://prove2.me/submissions/ec47c95b-4e74-4e11-adc4-9e4e561158af

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_EquiMMS
import Definitions.Def_RequestProject_TwoThirdsLoss
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ)
    (hE : ∀ i, Nonempty (EquiMMS (v i) p (MMS n (v i) p) n)) :
    Losses v p Finset.univ Finset.univ (0 : ℝ) := by
  classical
  refine ⟨fun _ => ∅, fun _ => ∅, fun _ => 0, fun b _ => ⟨rfl, rfl, rfl⟩, fun b => by simp,
    fun b b' _ => by simp, fun b => by simp, by simp, fun b => le_refl 0, by simp, ?_⟩
  intro i _
  obtain ⟨E⟩ := hE i
  exact ⟨E, fun b hb => absurd (Finset.mem_univ b) hb⟩
end FairSelling
