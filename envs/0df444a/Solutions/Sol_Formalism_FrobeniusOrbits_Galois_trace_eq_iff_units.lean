-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Galois.trace_eq_iff_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:37:26.964933+00:00
-- url     : https://prove2.me/submissions/863d1bf0-d009-4b5f-aed6-293b5f08d0b5

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_trace_eq_iff

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
open Formalism.FrobeniusOrbits.Galois
variable {K : Type*} [Field K] {N : ℕ} [NeZero N] {ζ : K}
namespace Formalism.FrobeniusOrbits.Galois
theorem _root_.solution (hζ : IsPrimitiveRoot ζ N) (u c : (ZMod N)ˣ) :
    ζ ^ (u : ZMod N).val + ζ⁻¹ ^ (u : ZMod N).val = ζ ^ (c : ZMod N).val + ζ⁻¹ ^ (c : ZMod N).val ↔
      u = c ∨ u = -c := by
  rw [trace_eq_iff hζ, Units.ext_iff, Units.ext_iff, Units.val_neg]
end Formalism.FrobeniusOrbits.Galois
