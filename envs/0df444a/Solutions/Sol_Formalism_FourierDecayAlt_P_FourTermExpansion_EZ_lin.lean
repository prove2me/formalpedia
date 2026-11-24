-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FourTermExpansion.EZ_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:42:21.931714+00:00
-- url     : https://prove2.me/submissions/45ad99b3-f867-4d3d-abfe-81b4f09b8823

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourTermExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_antihermitian_part_mem_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_hermitian_part_mem_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_rdV_fun_add


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
theorem _root_.solution {Φ₁ Φ₂ : Mat k r → E} {g : Mat k r} (h₁ : Loc 1 Φ₁ g) (h₂ : Loc 1 Φ₂ g) (hgG : g ∈ GV k r)
    (c : ℂ) (Z : Mat k r) : EZ Z (fun x => Φ₁ x + c • Φ₂ x) g = EZ Z Φ₁ g + c • EZ Z Φ₂ g := by
  show RdV _ (fun x => Φ₁ x + c • Φ₂ x) g + Complex.I • RdV _ (fun x => Φ₁ x + c • Φ₂ x) g =
    (RdV _ Φ₁ g + Complex.I • RdV _ Φ₁ g) + c • (RdV _ Φ₂ g + Complex.I • RdV _ Φ₂ g)
  rw [rdV_fun_add h₁ h₂ hgG (hermitian_part_mem_lie Z), rdV_fun_add h₁ h₂ hgG (antihermitian_part_mem_lie Z)]
  module
end Formalism.FourierDecayAlt.P.FourTermExpansion
