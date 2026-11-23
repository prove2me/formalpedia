-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.iC_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:45:37.975045+00:00
-- url     : https://prove2.me/submissions/4a485bc6-dc94-44b3-a4de-de13f465f92c

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_iC_spec
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_coeLin_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x8
variable {K : Type} [CommRing K] (R : Subring K) {m : ℕ}
namespace Formalism.FourierDecayAlt.P.A5x8
theorem _root_.solution (Z : Matrix (Fin m) (Fin m) K) (hZ : IsInt R Z) (hd : IsUnit Z.det) :
    Function.Injective (iC R Z) := by
  intro β β' h
  obtain ⟨b, hb, rfl⟩ := iC_spec R Z hZ hd β
  obtain ⟨b', hb', rfl⟩ := iC_spec R Z hZ hd β'
  rw [h, ← hb'] at hb
  rw [P.coeLin_injective R hb]
end Formalism.FourierDecayAlt.P.A5x8
