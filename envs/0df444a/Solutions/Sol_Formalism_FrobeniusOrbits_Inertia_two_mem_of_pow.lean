-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Inertia.two_mem_of_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:15:34.832552+00:00
-- url     : https://prove2.me/submissions/842ff951-6924-4134-9137-2309b6f4c4a9

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition Formalism.FrobeniusOrbits.Galois
open Formalism.FrobeniusOrbits.Inertia
namespace Formalism.FrobeniusOrbits.Inertia
theorem _root_.solution {R : Type*} [CommRing R] [IsDomain R] (Q : Ideal R) :
    ∀ (i : ℕ) (η : R), η ^ (2 ^ i) = 1 → η ≠ 1 → η - 1 ∈ Q → (2 : R) ∈ Q := by
  intro i
  induction i with
  | zero =>
    intro η h1 hne _
    simp at h1
    exact absurd h1 hne
  | succ i ih =>
    intro η h1 hne hQ
    by_cases h2 : η ^ 2 = 1
    · have h3 : (η - 1) * (η + 1) = 0 := by linear_combination h2
      rcases mul_eq_zero.1 h3 with h | h
      · exact absurd (sub_eq_zero.1 h) hne
      · have hη : η = -1 := eq_neg_of_add_eq_zero_left h
        have h4 : (2 : R) = -(η - 1) := by rw [hη]; ring
        rw [h4]
        exact Q.neg_mem hQ
    · refine ih (η ^ 2) ?_ h2 ?_
      · rw [← pow_mul, ← pow_succ']
        exact h1
      · have h5 : η ^ 2 - 1 = (η + 1) * (η - 1) := by ring
        rw [h5]
        exact Q.mul_mem_left _ hQ
end Formalism.FrobeniusOrbits.Inertia
