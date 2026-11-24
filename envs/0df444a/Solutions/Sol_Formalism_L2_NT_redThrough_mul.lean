-- Prove2me | solution 1 for Formalism.L2.NT.redThrough_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:58:34.904113+00:00
-- url     : https://prove2.me/submissions/16c60ffa-1686-4c77-a809-9a88698d83b8

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
theorem _root_.solution {z w : Ω} (hz : z ∈ B) (hw : w ∈ B) :
    redThrough B κ (z * w) = redThrough B κ z * redThrough B κ w := by
  unfold redThrough
  rw [dif_pos (mul_mem hz hw), dif_pos hz, dif_pos hw, ← map_mul, ← map_mul]
  rfl
end Formalism.L2.NT
