-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.AbstractGermZero.germ_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:14:22.682049+00:00
-- url     : https://prove2.me/submissions/23d9dd6e-03b2-4ef1-b121-ea22e906e653

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_WipDworkInvG
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AbstractGermZeroCondition
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AbstractGermZero_intS_iff_alt
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AbstractGermZero_upG_subst
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intC_one
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intC_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intS_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Classical
namespace Formalism.L2.FormalSeriesBounds
namespace AbstractGermZero
open Formalism.IncomingBounds
variable {C : Type} [Field C] (V : VF C)
private theorem cc_subst_lemma {σ τ A : Type} [Finite σ] [CommRing A] (a : σ → MvPowerSeries τ A)
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f : MvPowerSeries σ A) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = MvPowerSeries.constantCoeff f := by
  rw [MvPowerSeries.constantCoeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)]
  rw [finsum_eq_single _ 0]
  · simp
  · intro e he
    obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext h)
    rw [map_finsuppProd]
    simp only [map_pow, ha, Finsupp.prod]
    rw [Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (zero_pow hs), smul_zero]
end AbstractGermZero
end Formalism.L2.FormalSeriesBounds
end
end

set_option autoImplicit false
noncomputable section
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.FormalSeriesBounds.AbstractGermZero
open Formalism.IncomingBounds
variable {C : Type} [Field C] (V : VF C)
namespace Formalism.L2.FormalSeriesBounds.AbstractGermZero
theorem _root_.solution {I : Fin 2 → Type} [∀ g, Fintype (I g)] (t t₂ h : ∀ g, I g → MvPowerSeries (I g) C)
    (ht0₂ : ∀ g c, MvPowerSeries.constantCoeff (t₂ g c) = 0)
    (hh0 : ∀ g c, MvPowerSeries.constantCoeff (h g c) = 0) (hhI : ∀ g c, IntS V (h g c))
    (hth : ∀ g c, t g c = MvPowerSeries.subst (t₂ g) (h g c)) :
    IntGerm V t ⊆ IntGerm V t₂ := by
  rintro F ⟨γ, hγ, rfl⟩
  have hX : ∀ (g : Fin 2) (x : I g),
      AltInv.IntS V.v (MvPowerSeries.X (⟨g, x⟩ : WV I) : MvPowerSeries (WV I) C) := fun g x => by
    intro μ
    rw [MvPowerSeries.coeff_X]
    split_ifs
    · exact AltInv.intC_one (v := V.v)
    · exact AltInv.intC_zero (v := V.v)
  have hH0 : ∀ w : WV I, MvPowerSeries.constantCoeff (upG w.1 (h w.1 w.2)) = 0 := fun w => by
    unfold upG
    rw [cc_subst_lemma _ (fun x => by simp)]
    exact hh0 w.1 w.2
  have hHI : ∀ w : WV I, IntS V (upG w.1 (h w.1 w.2)) := fun w => by
    rw [intS_iff_alt]
    exact AltInv.intS_subst (v := V.v) (fun x => by simp) (fun x => hX w.1 x)
      ((intS_iff_alt V _).mp (hhI w.1 w.2))
  have hH : MvPowerSeries.HasSubst (fun w : WV I => upG w.1 (h w.1 w.2)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hH0
  have hT₂ : MvPowerSeries.HasSubst (fun w : WV I => upG w.1 (t₂ w.1 w.2)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun w => by
      unfold upG
      rw [cc_subst_lemma _ (fun x => by simp)]
      exact ht0₂ w.1 w.2)
  refine ⟨MvPowerSeries.subst (fun w : WV I => upG w.1 (h w.1 w.2)) γ, ?_, ?_⟩
  · exact AltInv.intS_subst (v := V.v) hH0 (fun w => (intS_iff_alt V _).mp (hHI w)) ((intS_iff_alt V γ).mp hγ)
  · rw [MvPowerSeries.subst_comp_subst_apply hH hT₂]
    congr 1
    funext w
    rw [upG_subst t₂ ht0₂, ← hth]
end Formalism.L2.FormalSeriesBounds.AbstractGermZero
