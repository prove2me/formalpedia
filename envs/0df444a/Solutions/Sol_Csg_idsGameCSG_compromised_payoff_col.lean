-- Prove2me | solution 1 for Csg.idsGameCSG_compromised_payoff_col
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:57:06.553605+00:00
-- url     : https://prove2.me/submissions/bc514251-c1cc-4af7-928a-dcd68c6689fd

import Definitions.Def_Csg_IntrusionDetection
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_IntrusionDetectionReach
import Theorems.Thm_Csg_idsGameCSG_stageGame_A
import Theorems.Thm_Csg_CSG_bwInd_zero
import Theorems.Thm_Csg_policyAction_sum
attribute [local simp] Csg.CSG.bwInd_zero



set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (b : IDSState → Set.Icc (0 : ℝ) 1)
    {q' : AttackAction → ℝ} (hq' : q' ∈ stdSimplex ℝ AttackAction) :
    (idsGameCSG.stageGame .compromised (fun s' => (b s' : ℝ))).payoff idsUnifP q' =
      ((b .healthy : ℝ) + (b .compromised : ℝ)) / 2 := by
  have hinner : ∀ a2, ∑ a1, idsUnifP a1 *
      (idsGameCSG.stageGame .compromised (fun s' => (b s' : ℝ))).A a1 a2 =
        ((b .healthy : ℝ) + (b .compromised : ℝ)) / 2 := by
    intro a2
    rw [policyAction_sum]
    cases a2 <;> simp [idsGameCSG_stageGame_A, idsNext, idsUnifP] <;> ring
  rw [MatrixGame.payoff_eq_sum_mul']
  calc ∑ a2, (∑ a1, idsUnifP a1 *
        (idsGameCSG.stageGame .compromised (fun s' => (b s' : ℝ))).A a1 a2) * q' a2
      = ∑ a2, (((b .healthy : ℝ) + (b .compromised : ℝ)) / 2) * q' a2 :=
        Finset.sum_congr rfl fun a2 _ => by rw [hinner a2]
    _ = (((b .healthy : ℝ) + (b .compromised : ℝ)) / 2) * ∑ a2, q' a2 := by
        rw [← Finset.mul_sum]
    _ = ((b .healthy : ℝ) + (b .compromised : ℝ)) / 2 := by rw [hq'.2, mul_one]
end Csg
