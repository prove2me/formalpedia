-- Prove2me | solution 1 for Formalism.MainNotions.MassRatioZetaBound.mass_ratio_rhs_le_factorial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:29:58.207373+00:00
-- url     : https://prove2.me/submissions/e2074778-8b43-4e41-afc5-8f374cf238cc

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBound
import Theorems.Thm_Formalism_MainNotions_MassRatioZetaBound_lValEta_le
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
open Formalism Formalism.MainNotions Formalism.MainNotions.MassRatioZetaBound
open NumberField
variable {K : Type*} [Field K] [NumberField K]
namespace Formalism.MainNotions.MassRatioZetaBound
theorem _root_.solution [StarRing K] {M : ℕ} (hM : 3 ≤ M) :
    Formalism.HermitianLatticesTheory.massRatioRightSide K M ≤
      ((((M - 1).factorial : ℕ) : ℝ) * (Formalism.HermitianLatticesTheory.vInv K / Real.pi) ^ M) ^ Formalism.HermitianLatticesTheory.fDeg K *
        Real.exp (2 * ((Module.finrank ℚ K : ℝ) * zetaGL3GL2)) := by
  unfold Formalism.HermitianLatticesTheory.massRatioRightSide
  have hv : 0 ≤ Formalism.HermitianLatticesTheory.vInv K := by
    have := one_le_two_vInv (K := K); linarith
  set a : ℝ := ((((M - 1).factorial : ℕ) : ℝ) * (Formalism.HermitianLatticesTheory.vInv K / Real.pi) ^ M) ^ Formalism.HermitianLatticesTheory.fDeg K with ha
  have ha0 : 0 ≤ a := by positivity
  set b : ℝ := Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) with hb
  have hb1 : 1 ≤ b := Real.one_le_sqrt.2 (one_le_pow₀ one_le_two_vInv)
  have hB0 : 0 ≤ Real.exp (2 * ((Module.finrank ℚ K : ℝ) * zetaGL3GL2)) := (Real.exp_pos _).le
  calc a / b * Formalism.HermitianLatticesTheory.lValEta K M ≤ a / b * Real.exp (2 * ((Module.finrank ℚ K : ℝ) * zetaGL3GL2)) :=
        mul_le_mul_of_nonneg_left (lValEta_le hM) (div_nonneg ha0 (by linarith))
    _ ≤ a * Real.exp (2 * ((Module.finrank ℚ K : ℝ) * zetaGL3GL2)) :=
        mul_le_mul_of_nonneg_right (div_le_self ha0 hb1) hB0
end Formalism.MainNotions.MassRatioZetaBound
