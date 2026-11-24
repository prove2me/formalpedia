-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FourTermExpansion.EZ_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:40:55.905843+00:00
-- url     : https://prove2.me/submissions/431950d7-669a-4ff5-af05-24723415914b

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourTermExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_rdV_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_antihermitian_part_mem_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_hermitian_part_mem_lie


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FourTermExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.FourTermExpansion
theorem _root_.solution {Φ₁ Φ₂ : Mat k r → E} {U : Set (Mat k r)} (hU : IsOpen U) {g : Mat k r} (hg : g ∈ U)
    (hgG : g ∈ GV k r) (he : ∀ x ∈ U, x ∈ GV k r → Φ₁ x = Φ₂ x) (Z : Mat k r) : EZ Z Φ₁ g = EZ Z Φ₂ g := by
  show RdV _ Φ₁ g + Complex.I • RdV _ Φ₁ g = RdV _ Φ₂ g + Complex.I • RdV _ Φ₂ g
  rw [rdV_congr hU hg hgG (hermitian_part_mem_lie Z) he, rdV_congr hU hg hgG (antihermitian_part_mem_lie Z) he]
end Formalism.FourierDecayAlt.P.FourTermExpansion
