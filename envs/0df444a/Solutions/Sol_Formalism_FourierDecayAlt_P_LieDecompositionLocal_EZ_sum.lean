-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LieDecompositionLocal.EZ_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:53:59.392277+00:00
-- url     : https://prove2.me/submissions/ce229d3b-e16f-4a75-a011-8d7b05f76dae

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_EZ_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_EZ_rsmul
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_EZ_smul

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
theorem _root_.solution {Φ : Mat k r → E} {g : Mat k r} (hloc : Loc 1 Φ g) (hgG : g ∈ GV k r) {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) (Z : ι → Mat k r) :
    EZ (∑ i ∈ s, c i • Z i) Φ g = ∑ i ∈ s, c i • EZ (Z i) Φ g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have := EZ_rsmul hloc hgG 0 (0 : Mat k r)
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, EZ_add hloc hgG, EZ_smul hloc hgG, ih]
end Formalism.FourierDecayAlt.P.LieDecompositionLocal
