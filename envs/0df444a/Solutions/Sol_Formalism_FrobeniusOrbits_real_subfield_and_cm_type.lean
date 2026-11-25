-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.real_subfield_and_cm_type
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:55:59.453549+00:00
-- url     : https://prove2.me/submissions/400267f6-5e11-44d4-b510-bcb27c612b87

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_RealCyclotomicSubfield
import Theorems.Thm_Formalism_FrobeniusOrbits_real_subfield_of_galois_spec
import Theorems.Thm_Formalism_FrobeniusOrbits_hostCMType_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Polynomial
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.FrobeniusOrbits
theorem _root_.solution (hGal : HostGalois) (hSpec : HostGalSpec) : TwoPowerCyclotomicLayerRealSubfieldCharacterization ∧ HostCMType := by
  exact ⟨real_subfield_of_galois_spec hSpec, hostCMType_of hGal hSpec⟩
end Formalism.FrobeniusOrbits
