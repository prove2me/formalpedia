-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.hcl_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:29:16.977796+00:00
-- url     : https://prove2.me/submissions/a0d1fd7b-1ef2-49b2-9d29-2dc9901e5a40

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ConjReal
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_RealCyclotomicSubfield
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum

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
theorem _root_.solution (u : (ZMod (2 ^ (e + 2)))ˣ) : hcl e (-u) = hcl e u := by
  unfold hcl
  rw [QuotientGroup.eq, Subgroup.mem_zpowers_iff]
  exact ⟨1, by simp⟩
end Formalism.FrobeniusOrbits
