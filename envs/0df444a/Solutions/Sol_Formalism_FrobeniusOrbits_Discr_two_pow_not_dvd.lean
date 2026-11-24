-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Discr.two_pow_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:40.791741+00:00
-- url     : https://prove2.me/submissions/13e26472-2eb6-4b66-95d9-a446e97fd7e2

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_DiscriminantRealSubfield

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
open Formalism.FrobeniusOrbits.Discr
namespace Formalism.FrobeniusOrbits.Discr
theorem _root_.solution (e : ℕ) : ¬ (2 ^ (e + 2)) ∣ 2 := by
  intro h
  have h1 := Nat.le_of_dvd (by norm_num) h
  have h2 : 4 ≤ 2 ^ (e + 2) := by
    have := Nat.one_le_two_pow (n := e)
    rw [pow_succ, pow_succ]
    omega
  omega
end Formalism.FrobeniusOrbits.Discr
