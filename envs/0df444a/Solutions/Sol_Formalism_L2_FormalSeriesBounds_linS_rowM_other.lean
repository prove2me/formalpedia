-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.linS_rowM_other
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:13:25.037655+00:00
-- url     : https://prove2.me/submissions/88525eaa-0097-4588-97b8-5563937c338f

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_one_sub_ne
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_toW_same
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_toW_other
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.BaseCaseIdentities (OrdGE NoConst)
variable {C : Type} [Field C] {I : Fin 2 → Type} [∀ g, Fintype (I g)] {ι ι' : Type} [Fintype ι]
  [Fintype ι']
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (g : Fin 2) (e : ι → I g → C) (v' : ι' → I (1 - g) → C) (x : I (1 - g)) :
    linS (rowM g e v') (⟨1 - g, x⟩ : WV I) =
      rename (Function.Embedding.inr : ι' ↪ ι ⊕ ι') (linS v' x) := by
  unfold linS rowM
  rw [Fintype.sum_sum_type, map_sum]
  have h2 : ∑ c : ι, (Sum.elim (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) (Sum.inl c)
      (⟨1 - g, x⟩ : WV I)) • (X (Sum.inl c) : MvPowerSeries (ι ⊕ ι') C) = 0 := by
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [Sum.elim_inl, toW_other _ _ (one_sub_ne g), zero_smul]
  rw [h2, zero_add]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Sum.elim_inr, toW_same, map_smul, rename_X]
  rfl
end Formalism.L2.FormalSeriesBounds
