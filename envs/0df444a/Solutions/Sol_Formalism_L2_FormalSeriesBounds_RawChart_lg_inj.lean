-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RawChart.lg_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:26:33.098048+00:00
-- url     : https://prove2.me/submissions/d1d9c295-736a-47c2-b76c-07e679bab955

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeOfPowEqOne
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst


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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
open Formalism.L2.FormalSeriesBounds.RawChart
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)
namespace Formalism.L2.FormalSeriesBounds.RawChart
theorem _root_.solution (hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0)
    (hexlg : ∀ i, MvPowerSeries.subst X.lg (X.ex i) = (MvPowerSeries.X i : MvPowerSeries κ C))
    {γ γ' : κ → PowerSeries C} (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0)
    (hγ' : ∀ i, PowerSeries.constantCoeff (γ' i) = 0)
    (h : ∀ i, alongCv γ (X.lg i) = alongCv γ' (X.lg i)) : γ = γ' := by
  have key : ∀ (δ : κ → PowerSeries C), (∀ i, PowerSeries.constantCoeff (δ i) = 0) → ∀ i,
      δ i = MvPowerSeries.subst (fun j => alongCv δ (X.lg j)) (X.ex i) := by
    intro δ hδ i
    have hS := MvPowerSeries.hasSubst_of_constantCoeff_zero hδ
    have e1 : MvPowerSeries.subst δ (MvPowerSeries.subst X.lg (X.ex i)) = δ i := by
      rw [hexlg i, MvPowerSeries.subst_X hS]
    rw [← e1, MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hlg0) hS]
    rfl
  funext i
  rw [key γ hγ i, key γ' hγ' i]
  simp only [h]
end Formalism.L2.FormalSeriesBounds.RawChart
