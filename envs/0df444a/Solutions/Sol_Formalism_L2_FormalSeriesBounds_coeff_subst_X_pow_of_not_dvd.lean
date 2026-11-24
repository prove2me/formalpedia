-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.coeff_subst_X_pow_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:37:21.032059+00:00
-- url     : https://prove2.me/submissions/26faa5ff-8994-455f-af66-36c960e9f1de

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstMemTypeSetOfNonneg
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
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {l : ℕ} (hl : 0 < l) (f : PowerSeries C) (m : ℕ) (hm : ¬ l ∣ m) :
    PowerSeries.coeff m (PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) f) = 0 := by
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hl.ne']))]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  rw [← pow_mul, PowerSeries.coeff_X_pow, if_neg, smul_zero]
  rintro rfl
  exact hm (dvd_mul_right l d)
end Formalism.L2.FormalSeriesBounds
