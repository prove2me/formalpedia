-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.inv_exists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:17:25.300728+00:00
-- url     : https://prove2.me/submissions/ebdd13bd-4b38-4fcc-9d7f-2a52beb6b3bb

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_right_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_left_eq

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
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.A5x8
theorem _root_.solution {w : Point K} (p p₁ : lowW K w.1 w.2 × upUniG K w.1.sum)
    (h : toCos R p = toCos R p₁) :
    ∃ a ∈ intSub R (lowW K w.1 w.2), ∃ b ∈ intSub R (upUniG K w.1.sum),
      p₁ = (a * p.1, p.2 * b) := by
  unfold toCos at h
  obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h
  obtain ⟨a, ha, e1⟩ := (sec_right_eq _ _ _).1 h1
  obtain ⟨b, hb, e2⟩ := (sec_left_eq _ _ _).1 h2
  exact ⟨a, ha, b, hb, Prod.ext e1 e2⟩
end Formalism.FourierDecayAlt.P.A5x8
