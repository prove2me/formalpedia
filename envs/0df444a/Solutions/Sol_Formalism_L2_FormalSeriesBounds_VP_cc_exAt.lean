-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.cc_exAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:43:48.789148+00:00
-- url     : https://prove2.me/submissions/d1e3072d-adc9-4b73-9ac6-fe0f3a90fc75

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoordinateChangeComp1IntertwinesAction
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValueEquationOfProjectors
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_EqOn_prod
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_IsIU_prod
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_prod
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_cc_e
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
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ τ' : Type}
variable (Y : FBChart C V O dd)
namespace Formalism.L2.FormalSeriesBounds.VP
theorem _root_.solution {a : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin dd) :
    MvPowerSeries.constantCoeff (exAt Y a i) = 0 := by
  unfold exAt
  rw [MvPowerSeries.constantCoeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  by_cases hd : d = 0
  · subst hd
    simp [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, cc_e Y i]
  · obtain ⟨s, hs⟩ := Finsupp.ne_iff.mp hd
    have h0 : MvPowerSeries.constantCoeff (d.prod fun s e => a s ^ e) = 0 := by
      rw [map_finsuppProd]
      apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs)
      show MvPowerSeries.constantCoeff (a s ^ d s) = 0
      rw [map_pow, ha s, zero_pow hs]
    rw [h0, smul_zero]
end Formalism.L2.FormalSeriesBounds.VP
