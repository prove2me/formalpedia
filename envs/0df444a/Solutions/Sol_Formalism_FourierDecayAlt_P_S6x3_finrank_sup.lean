-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x3.finrank_sup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:21:31.641584+00:00
-- url     : https://prove2.me/submissions/5cd92c07-7443-4f14-9332-dfe35a0a2b41

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FinrankLeOfMapLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x3
open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module
open scoped nonZeroDivisors
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
namespace Formalism.FourierDecayAlt.P.S6x3
theorem _root_.solution (N₁ N₂ : Submodule ℤ E) [Module.Finite ℤ N₁] [Module.Finite ℤ N₂]
    (h : Disjoint N₁ N₂) : finrank ℤ ↥(N₁ ⊔ N₂) = finrank ℤ N₁ + finrank ℤ N₂ := by
  have hinj : Function.Injective (N₁.subtype.coprod N₂.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_coprod_of_disjoint_range]
    · simp
    · simpa using h
  have := LinearMap.finrank_range_of_inj hinj
  rw [LinearMap.range_coprod, Submodule.range_subtype, Submodule.range_subtype,
    Module.finrank_prod] at this
  exact this
end Formalism.FourierDecayAlt.P.S6x3
