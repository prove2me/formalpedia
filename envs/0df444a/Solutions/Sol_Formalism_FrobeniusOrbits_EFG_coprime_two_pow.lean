-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.EFG.coprime_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:57:11.4208+00:00
-- url     : https://prove2.me/submissions/3d28bdd0-33e6-41f6-9ee8-ffc25bad0cef

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ConjReal
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardTrivialFirstComponent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.EFG
namespace Formalism.FrobeniusOrbits.EFG
theorem _root_.solution {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (e : ℕ) :
    Nat.Coprime p (2 ^ (e + 2)) :=
  Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
end Formalism.FrobeniusOrbits.EFG
