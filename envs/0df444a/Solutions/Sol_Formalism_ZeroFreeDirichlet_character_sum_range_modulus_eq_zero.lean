-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.character_sum_range_modulus_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:44:12.239147+00:00
-- url     : https://prove2.me/submissions/8a7c844b-4ce3-4bf0-827f-d3213d1b7706

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LPartialSum
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LGrowth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∑ n ∈ range q, χ (n : ZMod q) = 0 := by
  have hbij : Function.Bijective (fun i : Fin q => ((i : ℕ) : ZMod q)) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun a b hab => Fin.ext ?_, by simp [ZMod.card]⟩
    have h1 := congrArg ZMod.val hab
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] using h1
  rw [Finset.sum_range, Fintype.sum_bijective _ hbij (fun i => χ ((i : ℕ) : ZMod q)) χ (fun _ => rfl)]
  exact MulChar.sum_eq_zero_of_ne_one hχ
end Formalism.ZeroFreeDirichlet
