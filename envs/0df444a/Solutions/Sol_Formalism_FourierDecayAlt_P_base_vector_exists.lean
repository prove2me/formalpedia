-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.base_vector_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:24:29.684339+00:00
-- url     : https://prove2.me/submissions/2ba6af82-c729-440c-9a5a-fb02faffe3f3

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingConstruction
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_herm_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.B2.ZExists := by
  intro k r
  constructor
  · intro i hi
    simp only [bvec]
    rw [Pi.single_apply, if_neg]
    intro h; subst h; simp [wI] at hi
  · simp only [Tz, bvec]
    rw [SettingConstruction.herm_single]
    simp [Hpk, wI]
end Formalism.FourierDecayAlt.P
