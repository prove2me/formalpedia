-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianProjections.pow_eq_zero_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:26:15.933927+00:00
-- url     : https://prove2.me/submissions/dd28ec5a-8e94-482e-ac05-adde167c3cd5

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormBasics

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianProjections
namespace Formalism.FourierDecayAlt.P.HermitianProjections
theorem _root_.solution {R : Type*} [MonoidWithZero R] {x : R} {p q : ℕ} (h : x ^ p = 0)
    (hpq : p ≤ q) : x ^ q = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hpq
  rw [pow_add, h, zero_mul]
end Formalism.FourierDecayAlt.P.HermitianProjections
