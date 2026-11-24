-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FourTermExpansion.EZ_smul_fun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:34:46.236206+00:00
-- url     : https://prove2.me/submissions/b16b0c54-5d5c-4cf8-845f-f08c5f23ab33

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourTermExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_loc_hasDerivAt
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
theorem _root_.solution {Φ : Mat k r → E} {g : Mat k r} (h : Loc 1 Φ g) (hgG : g ∈ GV k r) (c : ℂ)
    (Z : Mat k r) : EZ Z (fun x => c • Φ x) g = c • EZ Z Φ g := by
  have e1 : RdV (hpart1 (Hpk k r) Z) (fun x => c • Φ x) g = c • RdV (hpart1 (Hpk k r) Z) Φ g :=
    ((loc_hasDerivAt le_rfl h hgG (hermitian_part_mem_lie Z)).const_smul c).deriv
  have e2 : RdV (hpart2 (Hpk k r) Z) (fun x => c • Φ x) g = c • RdV (hpart2 (Hpk k r) Z) Φ g :=
    ((loc_hasDerivAt le_rfl h hgG (antihermitian_part_mem_lie Z)).const_smul c).deriv
  show RdV _ (fun x => c • Φ x) g + Complex.I • RdV _ (fun x => c • Φ x) g =
    c • (RdV _ Φ g + Complex.I • RdV _ Φ g)
  rw [e1, e2]
  module
end Formalism.FourierDecayAlt.P.FourTermExpansion
