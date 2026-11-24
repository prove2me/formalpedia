-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.RealCyclotomicSubfield.finrank_cyc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:08:39.779061+00:00
-- url     : https://prove2.me/submissions/12ffeaac-717b-4673-932b-9787053e4405

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
theorem _root_.solution {e : ℕ} {ζ : L} (hζ : IsPrimitiveRoot ζ (2 ^ (e + 2))) :
    Module.finrank ℚ ℚ⟮ζ⟯ = 2 ^ (e + 1) := by
  have hint : IsIntegral ℚ ζ := Algebra.IsIntegral.isIntegral ζ
  rw [IntermediateField.adjoin.finrank hint, ← Polynomial.cyclotomic_eq_minpoly_rat hζ (by positivity),
    Polynomial.natDegree_cyclotomic, Nat.totient_prime_pow Nat.prime_two (by omega)]
  have h3 : e + 2 - 1 = e + 1 := by omega
  rw [h3]
  simp
end Formalism.FrobeniusOrbits.RealCyclotomicSubfield
