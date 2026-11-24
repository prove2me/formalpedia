-- Prove2me | solution 1 for Formalism.L2.NT.tameQuot_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:57:35.269798+00:00
-- url     : https://prove2.me/submissions/c012a352-4d12-41f6-9178-e785153a4031

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
namespace Formalism.L2.NT
theorem _root_.solution {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (σ : Ω ≃ₐ[E] Ω) {y : Ω} {m p : ℕ}
    (hp : (p : Ω) ≠ 0) (hy : y ^ m = (p : Ω)) : (σ y / y) ^ m = 1 := by
  have hy0 : y ^ m ≠ 0 := hy ▸ hp
  rw [div_pow, ← map_pow, hy, map_natCast, div_self hp]
end Formalism.L2.NT
