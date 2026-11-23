-- Prove2me | solution 1 for Csg.idsGameCSG_compromised_payoff_row
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:57:02.797942+00:00
-- url     : https://prove2.me/submissions/3608f1e9-c921-4116-989b-5e92f44f6ef2

import Definitions.Def_Csg_IntrusionDetection
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_IntrusionDetectionReach
import Theorems.Thm_Csg_idsGameCSG_stageGame_A
import Theorems.Thm_Csg_CSG_bwInd_zero
import Theorems.Thm_Csg_attackAction_sum
attribute [local simp] Csg.CSG.bwInd_zero



set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (b : IDSState → Set.Icc (0 : ℝ) 1)
    {p' : PolicyAction → ℝ} (hp' : p' ∈ stdSimplex ℝ PolicyAction) :
    (idsGameCSG.stageGame .compromised (fun s' => (b s' : ℝ))).payoff p' idsUnifQ =
      ((b .healthy : ℝ) + (b .compromised : ℝ)) / 2 := by
  have hinner : ∀ a1, ∑ a2,
      (idsGameCSG.stageGame .compromised (fun s' => (b s' : ℝ))).A a1 a2 * idsUnifQ a2 =
        ((b .healthy : ℝ) + (b .compromised : ℝ)) / 2 := by
    intro a1
    rw [attackAction_sum]
    cases a1 <;> simp [idsGameCSG_stageGame_A, idsNext, idsUnifQ] <;> ring
  rw [MatrixGame.payoff_eq_sum_mul]
  calc ∑ a1, p' a1 * ∑ a2,
        (idsGameCSG.stageGame .compromised (fun s' => (b s' : ℝ))).A a1 a2 * idsUnifQ a2
      = ∑ a1, p' a1 * (((b .healthy : ℝ) + (b .compromised : ℝ)) / 2) :=
        Finset.sum_congr rfl fun a1 _ => by rw [hinner a1]
    _ = (∑ a1, p' a1) * (((b .healthy : ℝ) + (b .compromised : ℝ)) / 2) := by
        rw [← Finset.sum_mul]
    _ = ((b .healthy : ℝ) + (b .compromised : ℝ)) / 2 := by rw [hp'.2, one_mul]
end Csg
