-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.FormalGermZero.coeff_single_subst_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:07:07.279916+00:00
-- url     : https://prove2.me/submissions/6bfa3236-65d6-414f-962f-5ef9cef9653a

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AbstractGermZeroCondition
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartAdd
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffSingleSubstOfLowDegree
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FormalGermZero_coeff_single_subst_of_low_degree
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
open Formalism.L2.FormalSeriesBounds.FormalGermZero
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
namespace Formalism.L2.FormalSeriesBounds.FormalGermZero
theorem _root_.solution {σ τ : Type} [Finite σ] (a : σ → MvPowerSeries τ C)
    (ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f : MvPowerSeries σ C) (i : σ)
    (hf : ∀ μ : σ →₀ ℕ, μ.degree ≤ 1 → MvPowerSeries.coeff μ f = MvPowerSeries.coeff μ (MvPowerSeries.X i))
    (c : τ) :
    MvPowerSeries.coeff (Finsupp.single c 1) (MvPowerSeries.subst a f) =
      MvPowerSeries.coeff (Finsupp.single c 1) (a i) := by
  have ha : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  have hr : ∀ e : σ →₀ ℕ, e.degree < 2 → MvPowerSeries.coeff e (f - MvPowerSeries.X i) = 0 := by
    intro e he
    rw [map_sub, hf e (by omega), sub_self]
  have hsplit : f = MvPowerSeries.X i + (f - MvPowerSeries.X i) := by ring
  rw [hsplit, MvPowerSeries.subst_add ha, MvPowerSeries.subst_X ha, map_add,
    coeff_single_subst_of_low_degree a ha0 _ hr c, add_zero]
end Formalism.L2.FormalSeriesBounds.FormalGermZero
