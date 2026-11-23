-- Prove2me | solution 1 for Csg.idsGameCSG_compromised_stageValue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:59:09.71695+00:00
-- url     : https://prove2.me/submissions/ce8102e2-ac34-46cf-85b2-5d9ce47db0bb

import Definitions.Def_Csg_IntrusionDetection
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_IntrusionDetectionReach
import Theorems.Thm_Csg_idsUnifP_mem
import Theorems.Thm_Csg_idsUnifQ_mem
import Theorems.Thm_Csg_idsGameCSG_compromised_payoff_row
import Theorems.Thm_Csg_idsGameCSG_compromised_payoff_col
import Theorems.Thm_Csg_MatrixGame_value_unique


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (b : IDSState → Set.Icc (0 : ℝ) 1) :
    idsGameCSG.stageValue .compromised (fun s' => (b s' : ℝ)) =
      ((b .healthy : ℝ) + (b .compromised : ℝ)) / 2 := by
  have huu : (idsGameCSG.stageGame .compromised (fun s' => (b s' : ℝ))).payoff idsUnifP idsUnifQ =
      ((b .healthy : ℝ) + (b .compromised : ℝ)) / 2 :=
    idsGameCSG_compromised_payoff_row b idsUnifP_mem
  have hrow : ∀ p' ∈ stdSimplex ℝ PolicyAction,
      (idsGameCSG.stageGame .compromised (fun s' => (b s' : ℝ))).payoff idsUnifP idsUnifQ ≤
        (idsGameCSG.stageGame .compromised (fun s' => (b s' : ℝ))).payoff p' idsUnifQ :=
    fun p' hp' => le_of_eq (huu.trans (idsGameCSG_compromised_payoff_row b hp').symm)
  have hcol : ∀ q' ∈ stdSimplex ℝ AttackAction,
      (idsGameCSG.stageGame .compromised (fun s' => (b s' : ℝ))).payoff idsUnifP q' ≤
        (idsGameCSG.stageGame .compromised (fun s' => (b s' : ℝ))).payoff idsUnifP idsUnifQ :=
    fun q' hq' => le_of_eq ((idsGameCSG_compromised_payoff_col b hq').trans huu.symm)
  have hval := (idsGameCSG.stageGame .compromised (fun s' => (b s' : ℝ))).value_unique
    idsUnifP_mem idsUnifQ_mem hrow hcol
  change (idsGameCSG.stageGame .compromised (fun s' => (b s' : ℝ))).value =
    ((b .healthy : ℝ) + (b .compromised : ℝ)) / 2
  rw [← hval]
  exact huu
end Csg
