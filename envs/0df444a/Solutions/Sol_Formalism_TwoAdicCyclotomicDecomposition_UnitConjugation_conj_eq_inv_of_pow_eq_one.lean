-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.UnitConjugation.conj_eq_inv_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:37:30.427826+00:00
-- url     : https://prove2.me/submissions/69d4687a-36ed-42e8-801f-4f9b4fb6d971

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
namespace Formalism.TwoAdicCyclotomicDecomposition.UnitConjugation
theorem _root_.solution {z : ℂ} {m : ℕ} (hm : m ≠ 0) (hz : z ^ m = 1) :
    starRingEnd ℂ z = z⁻¹ := by
  have h1 : ‖z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hz hm
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, h1]
  simp
end Formalism.TwoAdicCyclotomicDecomposition.UnitConjugation
