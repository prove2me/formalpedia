-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.AbstractGermZero.upG_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:47:14.188958+00:00
-- url     : https://prove2.me/submissions/7db82f77-da8a-4157-97ff-c4742af7cbe2

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_WipDworkInvG
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AbstractGermZeroCondition
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
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
theorem _root_.solution {I : Fin 2 → Type} [∀ g, Fintype (I g)] (t : ∀ g, I g → MvPowerSeries (I g) C)
    (ht0 : ∀ g c, MvPowerSeries.constantCoeff (t g c) = 0) (g : Fin 2) (γ : MvPowerSeries (I g) C) :
    MvPowerSeries.subst (fun w : WV I => upG w.1 (t w.1 w.2)) (upG g γ) = upG g (MvPowerSeries.subst (t g) γ) := by
  have hX : MvPowerSeries.HasSubst
      (fun x : I g => (MvPowerSeries.X (⟨g, x⟩ : WV I) : MvPowerSeries (WV I) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun x => by simp)
  have hT : MvPowerSeries.HasSubst (fun w : WV I => upG w.1 (t w.1 w.2)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun w => by
      unfold upG
      rw [cc_subst_lemma _ (fun x => by simp)]
      exact ht0 w.1 w.2)
  have ht : MvPowerSeries.HasSubst (t g) := MvPowerSeries.hasSubst_of_constantCoeff_zero (ht0 g)
  have e1 : upG g γ = MvPowerSeries.subst
      (fun x : I g => (MvPowerSeries.X (⟨g, x⟩ : WV I) : MvPowerSeries (WV I) C)) γ := rfl
  have e2 : upG g (MvPowerSeries.subst (t g) γ) = MvPowerSeries.subst
      (fun x : I g => (MvPowerSeries.X (⟨g, x⟩ : WV I) : MvPowerSeries (WV I) C)) (MvPowerSeries.subst (t g) γ) := rfl
  rw [e1, e2, MvPowerSeries.subst_comp_subst_apply hX hT, MvPowerSeries.subst_comp_subst_apply ht hX]
  congr 1
  funext x
  rw [MvPowerSeries.subst_X hT]
  try rfl
end Formalism.L2.FormalSeriesBounds.AbstractGermZero
