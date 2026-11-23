-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.finsum_of_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:45:36.76686+00:00
-- url     : https://prove2.me/submissions/a684bc01-8184-4627-8df1-d009fc57541f

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula

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
namespace Formalism.FourierDecayAlt.P.A5x8
theorem _root_.solution {X S : Type} (ι : S → X) (hι : Function.Injective ι) (t : X → ℂ)
    (ht : Function.support t ⊆ Set.range ι) : ∑ᶠ x, t x = ∑ᶠ s, t (ι s) := by
  have h1 : ∑ᶠ x ∈ Set.range ι, t x = ∑ᶠ x, t x := by
    rw [finsum_mem_def, Set.indicator_eq_self.mpr ht]
  have h2 : ∑ᶠ x ∈ Set.range ι, t x = ∑ᶠ s, t (ι s) := finsum_mem_range hι
  rw [← h1, h2]
end Formalism.FourierDecayAlt.P.A5x8
