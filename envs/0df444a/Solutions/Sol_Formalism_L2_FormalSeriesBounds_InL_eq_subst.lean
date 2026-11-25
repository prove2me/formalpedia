-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.InL.eq_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:47:54.956178+00:00
-- url     : https://prove2.me/submissions/af47f64d-0109-4583-b32e-f91011bacdd5

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeOfPowEqOne
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_dnL
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_subst_X_pow
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_subst_X_pow_of_not_dvd


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
namespace InL
theorem _root_.solution {l : ℕ} (hl : 0 < l) {f : PowerSeries C} (hf : InL l f) :
    f = PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) (dnL l f) := by
  ext m
  by_cases hm : l ∣ m
  · obtain ⟨k, rfl⟩ := hm
    rw [coeff_subst_X_pow hl, coeff_dnL]
  · rw [coeff_subst_X_pow_of_not_dvd hl _ _ hm, hf m hm]
end InL
end Formalism.L2.FormalSeriesBounds
