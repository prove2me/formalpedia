-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.alongCv_repar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:36:36.981799+00:00
-- url     : https://prove2.me/submissions/08ba0745-c1ba-48e7-bba1-712af09032b6

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstMemTypeSetOfNonneg
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
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {σ : Type} [Finite σ] {γ : σ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) {τ : PowerSeries C} (hτ : PowerSeries.constantCoeff τ = 0)
    (f : MvPowerSeries σ C) :
    alongCv (fun i => PowerSeries.subst τ (γ i)) f = PowerSeries.subst τ (alongCv γ f) := by
  unfold alongCv
  have hγs : MvPowerSeries.HasSubst γ := MvPowerSeries.hasSubst_of_constantCoeff_zero hγ
  have hτs : MvPowerSeries.HasSubst (fun _ : Unit => τ) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hτ)
  exact (MvPowerSeries.subst_comp_subst_apply hγs hτs f).symm
end Formalism.L2.FormalSeriesBounds
