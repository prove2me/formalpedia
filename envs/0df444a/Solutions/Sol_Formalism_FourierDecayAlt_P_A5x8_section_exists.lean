-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.section_exists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:06:02.121428+00:00
-- url     : https://prove2.me/submissions/df3385b1-e28f-4c00-8676-ad2da214bbc2

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_orbZ
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_phase
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_sigma_bij
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_addBlock_sum


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
theorem _root_.solution (h : Point K) (c : Kˣ) :
    ∃ σ : Par R h → lowW K (addBlock h 1 c).1 (addBlock h 1 c).2 × upUniG K (addBlock h 1 c).1.sum,
      Function.Bijective (fun t => toCos R (σ t)) ∧
      ∀ t, orbZ (addBlock h 1 c) (σ t) =
          bigZ (addBlock_sum h c) (orbZ h (rep R t.1)) (outV R t.2.1) (outV R t.2.2) (c : K) ∧
        ∀ ψ : AddChar K ℂ, phase ψ (σ t) =
          phase ψ (rep R t.1) * ψ (lastE (outV R t.2.1) + lastE (outV R t.2.2)) :=
  ⟨sec_sigma R h c, sec_sigma_bij R h c, fun t => ⟨sec_orbZ h c (rep R t.1) _ _, fun ψ =>
      sec_phase h c (rep R t.1) _ _ ψ⟩⟩
end Formalism.FourierDecayAlt.P.A5x8
