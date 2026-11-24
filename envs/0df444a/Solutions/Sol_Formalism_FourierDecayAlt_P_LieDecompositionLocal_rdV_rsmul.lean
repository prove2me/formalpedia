-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LieDecompositionLocal.rdV_rsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:47:56.811196+00:00
-- url     : https://prove2.me/submissions/3c4996bf-cbca-4ea7-8854-2d6641c9ed6a

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_rdV_eq_fderiv
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_inLie_rsmul


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
theorem _root_.solution {Φ : Mat k r → E} {g X : Mat k r} (hloc : Loc 1 Φ g) (hgG : g ∈ GV k r)
    (hX : inLie k r X) (c : ℝ) : RdV ((c : ℂ) • X) Φ g = c • RdV X Φ g := by
  obtain ⟨U, Φ', hU, hgU, hc, he⟩ := hloc
  rw [rdV_eq_fderiv le_rfl hU hgU hgG hc he hX,
    rdV_eq_fderiv le_rfl hU hgU hgG hc he (B4.inLie_rsmul hX c)]
  have : g * ((c : ℂ) • X) = c • (g * X) := by
    rw [Matrix.mul_smul]; rfl
  rw [this, map_smul]
end Formalism.FourierDecayAlt.P.LieDecompositionLocal
