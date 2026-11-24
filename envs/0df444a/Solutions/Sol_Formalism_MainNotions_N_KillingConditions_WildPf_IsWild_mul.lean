-- Prove2me | solution 1 for Formalism.MainNotions.N.KillingConditions.WildPf.IsWild.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:06:49.019308+00:00
-- url     : https://prove2.me/submissions/7aa81dcf-239e-4183-9069-a542dff4524f

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactRightVersion_Imports
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_WildPro
import Theorems.Thm_Formalism_MainNotions_N_KillingConditions_WildPf_IsWild_val_div

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.KillingConditions Formalism.MainNotions.N.KillingConditions.WildPf
variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω)
variable {A}
namespace Formalism.MainNotions.N.KillingConditions.WildPf
namespace IsWild
theorem _root_.solution {σ τ : Ω ≃ₐ[E] Ω} (hσ : IsWild A σ) (hτ : IsWild A τ) : IsWild A (σ * τ) := by
  intro y hy
  have hτy : τ y ≠ 0 := (map_ne_zero τ).2 hy
  have e : (σ * τ) y / y - 1 = (σ (τ y) / τ y - 1) * (τ y / y) + (τ y / y - 1) := by
    rw [AlgEquiv.mul_apply]
    field_simp
    ring
  rw [e]
  refine Valuation.map_add_lt _ ?_ (hτ y hy)
  rw [map_mul, hτ.val_div hy, mul_one]
  exact hσ _ hτy
end IsWild
end Formalism.MainNotions.N.KillingConditions.WildPf
