-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.intGerm_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:01:18.547608+00:00
-- url     : https://prove2.me/submissions/bcf20af5-5e6d-48cb-a0ba-3fd90f2610f4

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_subst_linS_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_subst_row_upG_self
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_subst_row_upG_other
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_rowIdx_self
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_rowIdx_other
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_rowIdx_injective
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_constantCoeff_ttPull
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_constantCoeff_upG
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_zero
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero


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
theorem _root_.solution (V : VF C) (t : ∀ g, I g → MvPowerSeries (I g) C)
    (ht0 : ∀ g c, constantCoeff (t g c) = 0) (g : Fin 2) (e : ι → I g → C)
    (v' : ι' → I (1 - g) → C) {K : MvPowerSeries (WV I) C} (hK : K ∈ IntGerm V t) :
    ∃ Kp : MvPowerSeries (I g ⊕ I (1 - g)) C, (∀ A, V.Ge 0 (coeff A Kp)) ∧
      subst (linS (rowM g e v')) K = subst (ttPull t g e v') Kp := by
  obtain ⟨γ, hγ, rfl⟩ := hK
  let f : WV I ↪ I g ⊕ I (1 - g) := ⟨rowIdx g, rowIdx_injective g⟩
  refine ⟨rename f γ, ?_, ?_⟩
  · intro A
    by_cases hA : A ∈ Set.range (Finsupp.mapDomain f)
    · obtain ⟨y, rfl⟩ := hA
      rw [← Finsupp.embDomain_eq_mapDomain, coeff_embDomain_rename]
      exact hγ y
    · rw [coeff_rename_eq_zero _ _ hA]
      exact VF.Ge.zero 0
  · rw [subst_linS_subst _ (fun s => constantCoeff_upG _ (ht0 _ _)), rename_eq_subst,
      subst_comp_subst_apply (HasSubst.X_comp _)
        (hasSubst_of_constantCoeff_zero (constantCoeff_ttPull t ht0 g e v'))]
    congr 1
    funext w
    rw [Function.comp_apply,
      subst_X (hasSubst_of_constantCoeff_zero (constantCoeff_ttPull t ht0 g e v'))]
    obtain ⟨g', x⟩ := w
    rcases finset_fin_two_eq_cases g g' with rfl | rfl
    · show subst _ (upG g' (t g' x)) = ttPull t g' e v' (rowIdx g' ⟨g', x⟩)
      rw [subst_row_upG_self, rowIdx_self]
      rfl
    · show subst _ (upG (1 - g) (t (1 - g) x)) = ttPull t g e v' (rowIdx g ⟨1 - g, x⟩)
      rw [subst_row_upG_other, rowIdx_other]
      rfl
end Formalism.L2.FormalSeriesBounds
