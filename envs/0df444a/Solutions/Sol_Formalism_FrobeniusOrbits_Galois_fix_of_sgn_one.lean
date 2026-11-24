-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Galois.fix_of_sgn_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:56:04.757151+00:00
-- url     : https://prove2.me/submissions/f18a0a5c-3660-48fc-8caf-cda7eebbc797

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois

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
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
namespace Formalism.FrobeniusOrbits.Galois
theorem _root_.solution {K : Type*} [Field K] [Algebra ℚ K] {σ : Gal(K/ℚ)} {x : K}
    (hs : sgn σ x = 1) : σ x = x := by
  rw [sgn.eq_1] at hs
  by_contra hne
  rw [if_neg hne] at hs
  exact absurd (congrArg Units.val hs) (by norm_num)
end Formalism.FrobeniusOrbits.Galois
