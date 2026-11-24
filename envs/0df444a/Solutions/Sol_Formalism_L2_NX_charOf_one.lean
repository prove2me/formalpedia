-- Prove2me | solution 1 for Formalism.L2.NX.charOf_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:14:04.38305+00:00
-- url     : https://prove2.me/submissions/3334f1b1-221b-4256-bda5-6babb88d2ccc

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
variable {ι : Type} [Fintype ι] {p : ι → ℕ} {r : ℕ}
namespace Formalism.L2.NX
theorem _root_.solution {K : Type} [Field K] {q : ℕ} (ζ : Kˣ) (hζ : ζ ^ q = 1) :
    charOf ζ hζ (Multiplicative.ofAdd 1) = ζ := by
  have h1 : (1 : ZMod q) = ((1 : ℤ) : ZMod q) := Int.cast_one.symm
  simp only [charOf, AddMonoidHom.toMultiplicativeLeft_apply_apply, toAdd_ofAdd]
  rw [h1, ZMod.lift_coe]
  simp
end Formalism.L2.NX
