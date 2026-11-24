-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.hcl_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:22:20.290963+00:00
-- url     : https://prove2.me/submissions/c0ae1e73-e0a4-46d1-8402-7d473d3a13d3

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ConjReal
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_RealCyclotomicSubfield
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Theorems.Thm_Formalism_FrobeniusOrbits_hcl_neg
import Theorems.Thm_Formalism_FrobeniusOrbits_hcl_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
variable {e : ℕ}
namespace Formalism.FrobeniusOrbits
theorem _root_.solution : hcl e (-1 : (ZMod (2 ^ (e + 2)))ˣ) = 1 := by
  rw [hcl_neg, hcl_one]
end Formalism.FrobeniusOrbits
