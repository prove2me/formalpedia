-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RowData.hPull_axis_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:08:52.788183+00:00
-- url     : https://prove2.me/submissions/f812563e-ea6a-4fe4-903f-f0feecea9561

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_one_sub_ne
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_toW_other
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_hPullW_eq
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_subst_linS_eq_zero

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
variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type}
  [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (Xr : RowData C V d I J) {ι ι' : Type} [Fintype ι]
  [Fintype ι']
namespace Formalism.L2.FormalSeriesBounds
namespace RowData
theorem _root_.solution (g : Fin 2) (a a' : ZMod d) (e : ι → I g → C)
    (v' : ι' → I (1 - g) → C) (A : ι ⊕ ι' →₀ ℕ) (hA : ∀ c, A (Sum.inl c) = 0) :
    coeff A (hPullW (Xr.hL g a a') (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b))) = 0 := by
  rw [hPullW_eq]
  refine coeff_subst_linS_eq_zero _ (fun w => w.1 = g) (fun x => ∃ c, x = Sum.inl c) ?_ _ ?_ A ?_
  · rintro ⟨g', x⟩ hw c hc
    have hw' : g' = g := hw
    subst hw'
    rcases c with c | b
    · exact absurd ⟨c, rfl⟩ hc
    · show toW (1 - g') (v' b) _ = 0
      rw [toW_other _ _ (one_sub_ne g').symm]
  · intro μ hμ
    refine Xr.hL_axes g a a' μ (Or.inr fun w hw => ?_)
    exact (finset_fin_two_eq_cases g w.1).resolve_left (hμ w hw)
  · rintro _ ⟨c, rfl⟩
    exact hA c
end RowData
end Formalism.L2.FormalSeriesBounds
