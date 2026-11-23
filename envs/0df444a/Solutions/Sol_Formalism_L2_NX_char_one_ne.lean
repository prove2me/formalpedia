-- Prove2me | solution 1 for Formalism.L2.NX.char_one_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:13:04.059853+00:00
-- url     : https://prove2.me/submissions/943880e5-3b23-4f5d-8764-a31ce1239a27

import Mathlib
import Definitions.Def_Formalism_AlgebraicWeights_IsAlgWeight
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs

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
theorem _root_.solution {K : Type} [Field K] {q : ℕ} [NeZero q] (θ : Multiplicative (ZMod q) →* Kˣ) (hθ : θ ≠ 1) :
    θ (Multiplicative.ofAdd 1) ≠ 1 := by
  intro h
  apply hθ
  refine MonoidHom.ext fun x => ?_
  have key : x = Multiplicative.ofAdd (1 : ZMod q) ^ (Multiplicative.toAdd x).val := by
    rw [← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]
  rw [MonoidHom.one_apply, key, map_pow, h, one_pow]
end Formalism.L2.NX
