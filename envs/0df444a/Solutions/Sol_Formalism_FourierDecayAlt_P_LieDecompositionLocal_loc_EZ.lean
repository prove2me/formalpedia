-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LieDecompositionLocal.loc_EZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:42:22.973869+00:00
-- url     : https://prove2.me/submissions/e813d697-a582-4325-8849-8cb7f467f678

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_hermitian_part_mem_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_antihermitian_part_mem_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_loc_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_loc_RdV


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
theorem _root_.solution {m : ℕ∞} {Φ : Mat k r → E} {g : Mat k r} (Z : Mat k r) (h : Loc (m + 1) Φ g) :
    Loc m (EZ Z Φ) g :=
  loc_add (loc_RdV (hermitian_part_mem_lie Z) h) (loc_RdV (antihermitian_part_mem_lie Z) h) Complex.I
end Formalism.FourierDecayAlt.P.LieDecompositionLocal
