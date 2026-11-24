-- Prove2me | solution 1 for Formalism.L2.NT.redThrough_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:19:57.685997+00:00
-- url     : https://prove2.me/submissions/7bf99fb3-e220-493d-8ac1-b3061194a73a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_RealCyclotomicTwoPower
import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs
import Theorems.Thm_Formalism_L2_NT_redThrough_mul
import Theorems.Thm_Formalism_L2_NT_redThrough_one

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
theorem _root_.solution {z : Ω} (hz : z ∈ B) (n : ℕ) : redThrough B κ (z ^ n) = redThrough B κ z ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, redThrough_one]
  | succ n ih => rw [pow_succ, redThrough_mul B κ (pow_mem hz n) hz, ih, pow_succ]
end Formalism.L2.NT
