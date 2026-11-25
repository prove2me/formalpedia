-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.subst_zeroPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:42:32.26614+00:00
-- url     : https://prove2.me/submissions/878ab932-e97d-469c-953f-b8433bc90836

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_PullbackLogCoordsEvalZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfUnitGerm
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_EqOn_prod
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_prod
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_hs
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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open Formalism.L2.FormalSeriesBounds.VP
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
namespace Formalism.L2.FormalSeriesBounds.VP
theorem _root_.solution {σ τ : Type} [Finite σ] (f : MvPowerSeries σ C) :
    MvPowerSeries.subst (fun _ : σ => (0 : MvPowerSeries τ C)) f = MvPowerSeries.C (MvPowerSeries.constantCoeff f) := by
  ext e
  rw [MvPowerSeries.coeff_subst (hs (fun _ => MvPowerSeries.constantCoeff_zero)), finsum_eq_single _ 0]
  · by_cases he : e = 0 <;> simp [he, MvPowerSeries.coeff_C, MvPowerSeries.coeff_one]
  · intro d hd
    obtain ⟨s, hs'⟩ : ∃ s, d s ≠ 0 := by
      by_contra h
      push_neg at h
      exact hd (Finsupp.ext h)
    have h0 : (d.prod fun _ n => (0 : MvPowerSeries τ C) ^ n) = 0 :=
      Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs') (zero_pow hs')
    simp [h0]
end Formalism.L2.FormalSeriesBounds.VP
