-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.invariant_integral_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:23:12.244125+00:00
-- url     : https://prove2.me/submissions/1515a9e7-3707-41d9-ada4-a6873872dd41

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInt
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_norm_pow_p_le_one
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_Pstep_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Finset
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution : InvInt := by
  intro p _ W ι _ _ _ E hE M hZ hD l L hL u hu
  have up : ∀ (a b : ℕ) (x : W), a ≤ b → (p : ℚ_[p]) ^ a • x ∈ M → (p : ℚ_[p]) ^ b • x ∈ M := by
    intro a b x hab hx
    have := hZ _ (norm_pow_p_le_one (p := p) (b - a)) _ hx
    rwa [smul_smul, ← pow_add, Nat.sub_add_cancel hab] at this
  have main : ∀ (L : List ι), L.Nodup → ∀ N, l + L.length - 1 ≤ N → ∀ u ∈ M,
      ((p : ℚ_[p]) ^ (L.length.choose 2 * Nat.log p N)) • InvOp E l L u ∈ M := by
    intro L
    induction L with
    | nil =>
      intro _ N _ u hu
      simpa [InvOp] using hu
    | cons z L ih =>
      intro hnd N hN u hu
      rw [List.nodup_cons] at hnd
      obtain ⟨hzL, hnd⟩ := hnd
      simp only [List.length_cons] at hN
      have hv := ih hnd N (by omega) u hu
      have hcard : L.toFinset.card = L.length := List.toFinset_card_of_nodup hnd
      have hz : z ∉ L.toFinset := by simpa using hzL
      have hP := Pstep_int hE hZ hD hz l hv
      rw [hcard] at hP
      have hP' := up _ (L.length * Nat.log p N) _
        (Nat.mul_le_mul_left _ (Nat.log_mono_right (by omega))) hP
      convert hP' using 1
      rw [InvOp, Module.End.mul_apply, map_smul, smul_smul, ← pow_add, List.length_cons,
        Nat.choose_succ_succ, Nat.choose_one_right]
      congr 2
      ring
  exact main L hL (l + L.length - 1) le_rfl u hu
end Formalism.InvariantFactorPaths.PW
