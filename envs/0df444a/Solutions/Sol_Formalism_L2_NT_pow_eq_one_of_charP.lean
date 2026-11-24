-- Prove2me | solution 1 for Formalism.L2.NT.pow_eq_one_of_charP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:58:33.97379+00:00
-- url     : https://prove2.me/submissions/fc60e93c-e67b-45f5-b711-e58bf1da7208

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_RealCyclotomicTwoPower
import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Polynomial
open Formalism Formalism.L2 Formalism.L2.NT
open Formalism.L2.Host
variable {Ω : Type} [Field Ω]
variable (B : ValuationSubring Ω) {l : ℕ} [Fact l.Prime] (κ : IsLocalRing.ResidueField B ≃+* Formalism.CyclotomicNorms.Fbar l)
namespace Formalism.L2.NT
theorem _root_.solution {k : Type} [Field k] (l : ℕ) [Fact l.Prime] [CharP k l] (y : k) (a m : ℕ)
    (h : y ^ (l ^ a * m) = 1) : y ^ m = 1 := by
  have h2 : (y ^ m - 1) ^ (l ^ a) = 0 := by
    rw [sub_pow_char_pow, one_pow, ← pow_mul, mul_comm, h, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) |>.mp h2)
end Formalism.L2.NT
