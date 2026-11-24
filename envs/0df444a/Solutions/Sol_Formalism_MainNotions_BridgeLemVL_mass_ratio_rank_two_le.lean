-- Prove2me | solution 1 for Formalism.MainNotions.BridgeLemVL.mass_ratio_rank_two_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:11:30.629985+00:00
-- url     : https://prove2.me/submissions/1d07bad2-836f-49a1-af9c-010ff967a1a8

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EulerFacMulConjInvSplit
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVL
import Theorems.Thm_Formalism_MainNotions_BridgeLemVL_lValEta_two_le
import Theorems.Thm_Formalism_MainNotions_MassRatioZetaBound_one_le_two_vInv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemVL
open NumberField Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.IdealNormInequalities
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.MainNotions.BridgeLemVL
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) :
    Formalism.HermitianLatticesTheory.massRatioRightSide K 2 ≤ ((Formalism.HermitianLatticesTheory.vInv K / Real.pi) ^ 2) ^ Formalism.HermitianLatticesTheory.fDeg K *
      Real.exp (2 * ((Module.finrank ℚ K : ℝ) * Z2)) := by
  unfold Formalism.HermitianLatticesTheory.massRatioRightSide
  have hv : 0 ≤ Formalism.HermitianLatticesTheory.vInv K := by
    have := Formalism.MainNotions.MassRatioZetaBound.one_le_two_vInv (K := K); linarith
  have e1 : (((Nat.factorial (2 - 1) : ℕ) : ℝ) * (Formalism.HermitianLatticesTheory.vInv K / Real.pi) ^ 2) =
      (Formalism.HermitianLatticesTheory.vInv K / Real.pi) ^ 2 := by norm_num
  rw [e1]
  set a : ℝ := ((Formalism.HermitianLatticesTheory.vInv K / Real.pi) ^ 2) ^ Formalism.HermitianLatticesTheory.fDeg K with ha
  have ha0 : 0 ≤ a := by positivity
  have hb1 : 1 ≤ Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) :=
    Real.one_le_sqrt.2 (one_le_pow₀ Formalism.MainNotions.MassRatioZetaBound.one_le_two_vInv)
  calc a / Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) * Formalism.HermitianLatticesTheory.lValEta K 2
      ≤ a / Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) *
          Real.exp (2 * ((Module.finrank ℚ K : ℝ) * Z2)) :=
        mul_le_mul_of_nonneg_left (lValEta_two_le hK) (div_nonneg ha0 (by linarith))
    _ ≤ a * Real.exp (2 * ((Module.finrank ℚ K : ℝ) * Z2)) :=
        mul_le_mul_of_nonneg_right (div_le_self ha0 hb1) (Real.exp_pos _).le
end Formalism.MainNotions.BridgeLemVL
