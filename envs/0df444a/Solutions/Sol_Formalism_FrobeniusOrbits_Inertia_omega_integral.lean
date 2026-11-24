-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Inertia.omega_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:14:12.547732+00:00
-- url     : https://prove2.me/submissions/9241b63d-a548-4135-93ac-60611d2afd16

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
theorem _root_.solution {F : Type} [Field F] [NumberField F] {r : ℕ} (hr4 : r % 4 = 3) {X : F}
    (hX : X ^ 2 = -(r : F)) : IsIntegral ℤ ((1 + X) / 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, r = 4 * k + 3 := ⟨r / 4, by omega⟩
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C ((k : ℤ) + 1), by monicity!, ?_⟩
  push_cast at hX
  rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C]
  simp only [algebraMap_int_eq, eq_intCast]
  push_cast
  linear_combination (1 / 4 : F) * hX
end Formalism.FrobeniusOrbits.Inertia
