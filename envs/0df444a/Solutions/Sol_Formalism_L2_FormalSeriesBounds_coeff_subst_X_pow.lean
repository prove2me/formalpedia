-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.coeff_subst_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:36:41.865657+00:00
-- url     : https://prove2.me/submissions/d7ca49c5-9566-4f07-af55-f362004cad16

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
theorem _root_.solution {l : ℕ} (hl : 0 < l) (f : PowerSeries C) (q : ℕ) :
    PowerSeries.coeff (l * q) (PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) f) = PowerSeries.coeff q f := by
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hl.ne'])), finsum_eq_single _ q]
  · rw [← pow_mul, PowerSeries.coeff_X_pow_self, smul_eq_mul, mul_one]
  · intro d hd
    rw [← pow_mul, PowerSeries.coeff_X_pow, if_neg, smul_zero]
    intro h
    exact hd (Nat.eq_of_mul_eq_mul_left hl h).symm
end Formalism.L2.FormalSeriesBounds
