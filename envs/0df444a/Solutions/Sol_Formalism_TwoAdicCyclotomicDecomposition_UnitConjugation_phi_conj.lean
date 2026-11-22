-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.UnitConjugation.phi_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:16:56.418017+00:00
-- url     : https://prove2.me/submissions/37af5966-be21-4753-a7f0-fdd3fd296a29

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_ConjEqInvOfPowEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition
open Formalism.TwoAdicCyclotomicDecomposition.UnitConjugation
variable {n q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
namespace Formalism.TwoAdicCyclotomicDecomposition.UnitConjugation
theorem _root_.solution (hq : 0 < q) (ha : a ^ 2 = -(q : L)) (φ : L →+* ℂ) :
    starRingEnd ℂ (φ a) = -φ a := by
  set z := φ a with hzdef
  have hz : z ^ 2 = -(q : ℂ) := by
    rw [hzdef, ← map_pow, ha, map_neg, map_natCast]
  have h1 : (starRingEnd ℂ z) ^ 2 = z ^ 2 := by
    rw [← map_pow, hz, map_neg, map_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h2 | h2
  · exfalso
    have hre := Complex.conj_eq_iff_re.1 h2
    have h3 : ((z.re ^ 2 : ℝ) : ℂ) = ((-(q : ℝ) : ℝ) : ℂ) := by
      push_cast; rw [hre]; exact hz
    have h4 := Complex.ofReal_injective h3
    have h5 : (0 : ℝ) < q := by exact_mod_cast hq
    nlinarith [sq_nonneg z.re]
  · exact h2
end Formalism.TwoAdicCyclotomicDecomposition.UnitConjugation
