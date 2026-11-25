-- Prove2me | solution 2 for Formalism.FourierDecayAlt.P.GroupGeneratedByExp.norm_pow_sub_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:46:29.451712+00:00
-- url     : https://prove2.me/submissions/13489626-7c78-4684-b6ad-cc04e48447fa

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GroupGeneratedByExp
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_GroupGeneratedByExp_norm_pow_mul_le__5d724b404c11
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_IsLin_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_Rep_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open Formalism.FourierDecayAlt.P.GroupGeneratedByExp
variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
namespace Formalism.FourierDecayAlt.P.GroupGeneratedByExp
theorem _root_.solution {a b : 𝔸} {q : ℝ} (hq : 1 ≤ q) (ha : ∀ u, ‖a * u‖ ≤ q * ‖u‖)
    (hb : ∀ u, ‖b * u‖ ≤ q * ‖u‖) (m : ℕ) :
    ‖a ^ m - b ^ m‖ ≤ (m : ℝ) * q ^ m * (‖a - b‖ * ‖(1 : 𝔸)‖) := by
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  induction m with
  | zero => simp
  | succ m ih =>
    have e : a ^ (m + 1) - b ^ (m + 1) = a * (a ^ m - b ^ m) + (a - b) * b ^ m := by
      rw [pow_succ', pow_succ']; noncomm_ring
    have h1 : ‖a * (a ^ m - b ^ m)‖ ≤ q * ((m : ℝ) * q ^ m * (‖a - b‖ * ‖(1 : 𝔸)‖)) :=
      (ha _).trans (mul_le_mul_of_nonneg_left ih hq0)
    have h2 : ‖b ^ m‖ ≤ q ^ (m + 1) * ‖(1 : 𝔸)‖ := by
      have := norm_pow_mul_le' hq0 hb m 1
      rw [mul_one] at this
      refine this.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      exact pow_le_pow_right₀ hq (Nat.le_succ m)
    have h3 : ‖(a - b) * b ^ m‖ ≤ ‖a - b‖ * (q ^ (m + 1) * ‖(1 : 𝔸)‖) :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
    rw [e]
    refine (norm_add_le _ _).trans ((add_le_add h1 h3).trans (le_of_eq ?_))
    push_cast
    ring
end Formalism.FourierDecayAlt.P.GroupGeneratedByExp
