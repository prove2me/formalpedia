-- Prove2me | solution 1 for Formalism.L2.Col.length_restrict_ow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:14:38.414796+00:00
-- url     : https://prove2.me/submissions/dad5f8f6-9644-4d25-99c6-9b41e0a9921b

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_LocalToGlobal_Columns_AlgebraMapMemMaximalIdealPowIff
import Theorems.Thm_Formalism_L2_Col_ow_smul_mem_of_length

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Col
variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable (w : HeightOneSpectrum (𝓞 K)) (Q : Type) [AddCommGroup Q] [Module (Ow w) Q] [Module (𝓞 K) Q]
  [IsScalarTower (𝓞 K) (Ow w) Q]
namespace Formalism.L2.Col
theorem _root_.solution : Module.length (𝓞 K) Q = Module.length (Ow w) Q := by
  by_cases hQ : Module.length (Ow w) Q = ⊤
  · have := Submodule.length_le_length_restrictScalars (𝓞 K) (⊤ : Submodule (Ow w) Q)
    rw [Submodule.restrictScalars_top, Module.length_top, Module.length_top, hQ] at this
    rw [hQ]
    exact top_le_iff.1 this
  · let e : Submodule (𝓞 K) Q ≃o Submodule (Ow w) Q :=
      { toFun := fun N => { N with smul_mem' := fun r _ hx => ow_smul_mem_of_length w Q hQ N r hx }
        invFun := fun N => N.restrictScalars (𝓞 K)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_rel_iff' := Iff.rfl }
    apply WithBot.coe_injective
    rw [Module.coe_length, Module.coe_length, Order.krullDim_eq_of_orderIso e]
end Formalism.L2.Col
