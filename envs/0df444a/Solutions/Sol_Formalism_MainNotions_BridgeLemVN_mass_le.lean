-- Prove2me | solution 1 for Formalism.MainNotions.BridgeLemVN.mass_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:04:01.940612+00:00
-- url     : https://prove2.me/submissions/d179a948-d5da-4691-8769-1b91a8d21d34

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVC
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVN
import Theorems.Thm_Formalism_MainNotions_BridgeLemVN_card_classReps_le
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemVN
open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.RankOne Formalism.MainNotions.BridgeLemVR
  Formalism.MainNotions.BridgeLemVC
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.MainNotions.BridgeLemVN
theorem _root_.solution (hK : IsCMUnram K) (h : K →ₗ⋆[K] K →ₗ[K] K) (h1 : h 1 1 ≠ 0) :
    mass h (1 : Submodule (𝓞 K) K) ≤ ((classNumber K * 2 ^ fDeg K : ℕ) : ℝ) := by
  unfold mass
  split_ifs with hex
  · refine le_trans ?_ (Nat.cast_le.2 (card_classReps_le hK h h1 _ hex.choose_spec))
    calc ∑ M ∈ hex.choose, ((Nat.card (autL h M) : ℕ) : ℝ)⁻¹ ≤ ∑ _M ∈ hex.choose, (1 : ℝ) := by
          refine Finset.sum_le_sum fun M _ => ?_
          rcases Nat.eq_zero_or_pos (Nat.card (autL h M)) with h0 | hpos
          · rw [h0]; simp
          · exact inv_le_one_of_one_le₀ (by exact_mod_cast hpos)
      _ = (hex.choose.card : ℝ) := by simp
  · positivity
end Formalism.MainNotions.BridgeLemVN
