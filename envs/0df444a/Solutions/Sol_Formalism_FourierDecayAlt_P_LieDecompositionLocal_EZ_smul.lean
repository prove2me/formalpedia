-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LieDecompositionLocal.EZ_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:33:52.508481+00:00
-- url     : https://prove2.me/submissions/f385c2f3-0ee2-41e5-b854-321bd263ff62

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_EZ_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_EZ_rsmul
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_EZ_I

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LieDecompositionLocal
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.LieDecompositionLocal
theorem _root_.solution {Φ : Mat k r → E} {g : Mat k r} (hloc : Loc 1 Φ g) (hgG : g ∈ GV k r) (c : ℂ)
    (Z : Mat k r) : EZ (c • Z) Φ g = c • EZ Z Φ g := by
  have hc : c • Z = (c.re : ℂ) • Z + (c.im : ℂ) • (Complex.I • Z) := by
    conv_lhs => rw [← Complex.re_add_im c]
    rw [add_smul, mul_smul]
  rw [hc, EZ_add hloc hgG, EZ_rsmul hloc hgG, EZ_rsmul hloc hgG, EZ_I hloc hgG, smul_smul,
    ← add_smul]
  rw [Complex.re_add_im]
end Formalism.FourierDecayAlt.P.LieDecompositionLocal
