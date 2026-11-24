-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.matrix_norm_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:11:08.372669+00:00
-- url     : https://prove2.me/submissions/fd65eaae-91ac-4d3a-88a8-e35c4d563633

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_hsblock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.B2.GNLower := by
  intro k r g hg
  have h := HermitianFormFactor.hsblock k r g hg
  have h0 : 0 ≤ B.gN g := Real.sqrt_nonneg _
  have h1 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by
    have : 1 ≤ 2 * r + k + 1 := Nat.le_add_left 1 _
    exact_mod_cast this
  nlinarith [sq_nonneg (B.gN (B2.Ppos k r * g * B2.Pneg k r))]
end Formalism.FourierDecayAlt.P
