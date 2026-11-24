-- Prove2me | solution 1 for Formalism.L2.NX.char_one_prim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:14:06.621035+00:00
-- url     : https://prove2.me/submissions/11e14e2a-ea38-44a1-b06b-48c949c5e13e

import Mathlib
import Definitions.Def_Formalism_AlgebraicWeights_IsAlgWeight
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs
import Theorems.Thm_Formalism_L2_NX_char_one_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.NX
variable {ι : Type} [Fintype ι] (p : ι → ℕ) (r : ℕ)
variable {r}
variable (r)
variable {p r}
variable (r)
variable {r}
variable (p r)
namespace Formalism.L2.NX
theorem _root_.solution {K : Type} [Field K] {q : ℕ} (hq : q.Prime) (θ : Multiplicative (ZMod q) →* Kˣ) (hθ : θ ≠ 1) :
    IsPrimitiveRoot (((θ (Multiplicative.ofAdd 1) : Kˣ)) : K) q := by
  haveI := Fact.mk hq
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have h1 : θ (Multiplicative.ofAdd 1) ^ q = 1 := by
    rw [← map_pow, ← ofAdd_nsmul, nsmul_one, ZMod.natCast_self, ofAdd_zero, map_one]
  rw [IsPrimitiveRoot.coe_units_iff, IsPrimitiveRoot.iff_orderOf]
  exact orderOf_eq_prime h1 (char_one_ne θ hθ)
end Formalism.L2.NX
