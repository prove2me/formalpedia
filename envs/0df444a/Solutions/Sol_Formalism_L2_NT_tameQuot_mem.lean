-- Prove2me | solution 1 for Formalism.L2.NT.tameQuot_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:14:18.376898+00:00
-- url     : https://prove2.me/submissions/c2efc267-c182-4196-bde2-0385ef4e5919

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_RealCyclotomicTwoPower
import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs
import Theorems.Thm_Formalism_L2_NT_mem_of_pow_eq_one
import Theorems.Thm_Formalism_L2_NT_tameQuot_pow

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
theorem _root_.solution {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω) (σ : Ω ≃ₐ[E] Ω) {y : Ω}
    {m p : ℕ} (hm : 0 < m) (hp : (p : Ω) ≠ 0) (hy : y ^ m = (p : Ω)) : σ y / y ∈ A :=
  mem_of_pow_eq_one A hm (tameQuot_pow σ hp hy)
end Formalism.L2.NT
