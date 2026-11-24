-- Prove2me | solution 1 for FairSelling.exists_MMS_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:33:49.756268+00:00
-- url     : https://prove2.me/submissions/3a610ba8-2065-4965-9231-fbfeb567e3e8

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Theorems.Thm_FairSelling_exists_reduced
import Theorems.Thm_FairSelling_config_sum_bound
import Theorems.Thm_FairSelling_util_swapOutcome
import Theorems.Thm_FairSelling_swapOutcome_valid
import Theorems.Thm_FairSelling_cutgive

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (v : Fin 2 → G → ℝ) (p : G → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g) :
    ∃ o : Outcome G 2, o.Valid p ∧ ∀ i, MMS 2 (v i) p ≤ util (v i) o i := by
  obtain ⟨Ac0, sc0, qc0, hcfg0, hcard0⟩ := exists_reduced (v 0) p (hv 0) hp
  obtain ⟨Ac1, sc1, qc1, hcfg1, hcard1⟩ := exists_reduced (v 1) p (hv 1) hp
  have hb0 := config_sum_bound (v 0) p (MMS 2 (v 0) p) Ac0 sc0 qc0 hcfg0
  have hb1 := config_sum_bound (v 1) p (MMS 2 (v 1) p) Ac1 sc1 qc1 hcfg1
  by_cases hcut : ∑ g ∈ sc0, p g ≤ ∑ g ∈ sc1, p g
  · obtain ⟨o, hov, h0, h1⟩ := cutgive v p hp Ac0 sc0 qc0 hcfg0 sc1 hcard1 hb1 hcut
    exact ⟨o, hov, fun i => by fin_cases i <;> assumption⟩
  · push_neg at hcut
    obtain ⟨o, hov, h0, h1⟩ := cutgive (fun i => v (Equiv.swap 0 1 i)) p hp Ac1 sc1 qc1
      (by simpa [Equiv.swap_apply_left] using hcfg1) sc0 hcard0
      (by simpa [Equiv.swap_apply_right] using hb0) (le_of_lt hcut)
    refine ⟨swapOutcome o, swapOutcome_valid p o hov, fun i => ?_⟩
    fin_cases i
    · rw [util_swapOutcome]; simpa [Equiv.swap_apply_left, Equiv.swap_apply_right] using h1
    · rw [util_swapOutcome]; simpa [Equiv.swap_apply_left, Equiv.swap_apply_right] using h0
end FairSelling
