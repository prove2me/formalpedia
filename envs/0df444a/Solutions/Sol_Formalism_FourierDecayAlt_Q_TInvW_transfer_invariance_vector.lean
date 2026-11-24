-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.transfer_invariance_vector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:34:39.825669+00:00
-- url     : https://prove2.me/submissions/9ead345b-ccc6-4cf1-9416-fb865864acdd

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_TransferInvarianceRestriction
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_glev_unit
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_inv_fix
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_glev_inv
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_glev_col
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_Q_TInvW_glev_row__71270a473e04
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_sum_posL
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_bvec_posL_outer
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_transfer_invariance_smooth
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_herm_uh
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_herm_col
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_herm_bv
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_uh_H_inv
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_posL_inj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.TInvW
theorem _root_.solution : StepVec := by
  intro k r z z' i hz hz'
  have bo : ∀ (a : Fin (mdim k r i)) q, (∀ c, q ≠ posL k r i c) →
      bvec q (posL k r i a) = 0 ∧ bvec (posL k r i a) q = 0 :=
    fun a q hq => bvec_posL_outer a q hq
  have blk_mul : ∀ s t : Mx k r, s ∈ Glev k r i → blk i (s * t) = blk i s * blk i t := by
    intro s t hs
    ext a b
    simp only [blk, Matrix.mul_apply]
    exact sum_posL (fun q => s (posL k r i a) q * t q (posL k r i b)) (fun q hq => by
      show s (posL k r i a) q * t q (posL k r i b) = 0
      rw [glev_col hs (posL k r i a) q hq, (bo a q hq).1, zero_mul])
  have blk_one : blk i (1 : Mx k r) = 1 := by
    ext a b
    simp only [blk, Matrix.one_apply]
    by_cases h : a = b
    · simp [h]
    · rw [if_neg (fun e => h (posL_inj e)), if_neg h]
  have mv_blk : ∀ s ∈ Glev k r i, ∀ v : Fin (2 * r + k + 1) → ℂ,
      (blk i s *ᵥ fun j => v (posL k r i j)) = fun j => (s *ᵥ v) (posL k r i j) := by
    intro s hs v
    funext a
    simp only [blk, Matrix.mulVec, dotProduct]
    exact (sum_posL (fun q => s (posL k r i a) q * v q) (fun q hq => by
      show s (posL k r i a) q * v q = 0
      rw [glev_col hs (posL k r i a) q hq, (bo a q hq).1, zero_mul])).symm
  have vm_blk : ∀ t ∈ Glev k r i, ∀ x : Fin (2 * r + k + 1) → ℂ,
      ((fun j => x (posL k r i j)) ᵥ* blk i t) = fun j => (x ᵥ* t) (posL k r i j) := by
    intro t ht x
    funext b
    simp only [blk, Matrix.vecMul, dotProduct]
    exact (sum_posL (fun q => x q * t q (posL k r i b)) (fun q hq => by
      show x q * t q (posL k r i b) = 0
      rw [glev_row' ht q (posL k r i b) hq, (bo b q hq).2, mul_zero])).symm
  have hS := transfer_invariance_smooth k r z i hz
  have hS' := transfer_invariance_smooth k r z' i hz'
  refine ⟨fun s hs g => ?_, fun s' hs' => ?_⟩
  · obtain ⟨hsG, hsf⟩ := hS.2 s hs
    have hu := glev_unit hsG
    have hsU : s ∈ UH (Hpk k r) := by
      simp only [Glev, Set.mem_setOf_eq] at hsG
      exact hsG.1
    have hinv : s⁻¹ *ᵥ fvec k r z i = fvec k r z i := inv_fix hu.2 hsf
    constructor
    · funext j
      simp only [yv]
      rw [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, hinv]
    · funext j
      simp only [ybv]
      conv_lhs => rw [← hsf]
      rw [← Matrix.mulVec_mulVec, herm_uh hsU]
  · obtain ⟨hsG, hsf⟩ := hS'.2 s' hs'
    have hu := glev_unit hsG
    have hiG := glev_inv hsG
    have hsU : s' ∈ UH (Hpk k r) := by
      have h0 := hsG
      simp only [Glev, Set.mem_setOf_eq] at h0
      exact h0.1
    refine ⟨?_, ?_, ?_, ?_, fun g hg => ⟨?_, ?_⟩⟩
    · rw [← blk_mul _ _ hsG, hu.1, blk_one]
    · rw [← blk_mul _ _ hiG, hu.2, blk_one]
    · unfold xv
      rw [mv_blk _ hsG, hsf]
    · unfold xbv
      simp only [herm_bv]
      rw [vm_blk _ hiG, Matrix.vecMul_vecMul, uh_H_inv hsU hu.1, ← Matrix.vecMul_vecMul, ← Matrix.star_mulVec, hsf]
    · unfold yv
      rw [mv_blk _ hsG]
      funext j
      rw [Matrix.mulVec_mulVec, Matrix.mul_inv_rev, ← Matrix.mul_assoc, hu.1, Matrix.one_mul]
    · unfold ybv
      simp only [herm_col]
      rw [vm_blk _ hiG]
      simp only [Matrix.vecMul_vecMul, Matrix.mul_assoc, hu.1, Matrix.mul_one]
end Formalism.FourierDecayAlt.Q.TInvW
