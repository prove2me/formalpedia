-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.RealCyclotomicSubfield.two_pow_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:05:50.400275+00:00
-- url     : https://prove2.me/submissions/855af674-dc6a-4e41-a152-c8e56b989501

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_RealCyclotomicSubfield

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
open Formalism.FrobeniusOrbits.RealCyclotomicSubfield
variable {L : Type} [Field L] [NumberField L]
namespace Formalism.FrobeniusOrbits.RealCyclotomicSubfield
theorem _root_.solution (e : ℕ) : ¬ (2 ^ (e + 2)) ∣ 2 := by
  intro h
  have h1 := Nat.le_of_dvd (by norm_num) h
  have h2 : 2 ^ 2 ≤ 2 ^ (e + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega
end Formalism.FrobeniusOrbits.RealCyclotomicSubfield
