-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x2.leastNorm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:39.301803+00:00
-- url     : https://prove2.me/submissions/455149d2-b711-47f1-a1e0-c0e4cd948366

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualIdealInclusion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualVolumePowerIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_dual_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x2
open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module MeasureTheory
open scoped nonZeroDivisors
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
namespace Formalism.FourierDecayAlt.P.S6x2
theorem _root_.solution (h1 : Formalism.FourierDecayAlt.L.DualLatticeInclusion) (hW : Formalism.FourierDecayAlt.W.NormLower) (h2 : PowConjStable)
    (h3 : Between) (hN : NormIdl) : LeastNorm := by
  intro E _ _ _ g ν s hg l hl hl0
  have h := hW E (dualIdl E g ν) l (dual_le E h1 h2 h3 g ν s hg hl) hl0
  have hn := hN E g (-1) (-(ν + 1)) hg
  refine le_trans (le_of_eq ?_) h
  unfold dualIdl
  rw [hn, zpow_neg, zpow_neg, zpow_neg, zpow_one, ← mul_inv, inv_pow, zpow_natCast]
end Formalism.FourierDecayAlt.P.S6x2
