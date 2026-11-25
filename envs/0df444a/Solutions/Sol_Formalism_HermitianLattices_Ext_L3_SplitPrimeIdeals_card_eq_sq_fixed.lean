-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals.card_eq_sq_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:03:51.675847+00:00
-- url     : https://prove2.me/submissions/3511335e-ba6e-413d-92bf-9a3c3e8ff177

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactSecondVariant_Imports
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NotIsPrimeMapOfSplit
import Theorems.Thm_Bl_general_b_fact_second_variant_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals
namespace Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals
theorem _root_.solution {k : Type*} [Field k] (τ : k →+* k) (hτ : ∀ x, τ (τ x) = x) (θ : k)
    (hθ : θ - τ θ ≠ 0) : Nat.card k = Nat.card {x : k // τ x = x} ^ 2 := by
  first | exact Bl.general_b_fact_second_variant.goal1 .. | (apply Bl.general_b_fact_second_variant.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second_variant.goal1 <;> assumption)
end Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals
