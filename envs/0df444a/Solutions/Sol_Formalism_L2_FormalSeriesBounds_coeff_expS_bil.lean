-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.coeff_expS_bil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:57:47.449637+00:00
-- url     : https://prove2.me/submissions/3d3b571d-d8c5-4af7-8588-3f3d2cf3d1af

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStab
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_mul_van_van
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_const
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_mul_right


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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries
variable {C : Type} [Field C]
variable [CharZero C] {n dd : ℕ}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {T : Set (Fin n × Fin dd)} {f : PS C n dd} (hf : Van T f) (e : Fin n × Fin dd →₀ ℕ)
    (P : Fin n × Fin dd) (he : ∀ s ∈ T, e s ≠ 0 → s = P) (hP : e P ≤ 1) (he0 : e ≠ 0) :
    coeff e (FB.expS C f) = coeff e f := by
  unfold FB.expS
  have h0 : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero hf.const
  rw [PowerSeries.coeff_subst h0, finsum_eq_single _ 1]
  · simp [PowerSeries.coeff_exp]
  · intro m hm
    rcases m with _ | _ | k
    · rw [pow_zero, coeff_one, if_neg he0, smul_zero]
    · exact absurd rfl hm
    · have e2 : f ^ (k + 1 + 1) = f * (f * f ^ k) := by ring
      rw [e2, coeff_mul_van_van hf (hf.mul_right _) e P he hP, smul_zero]
end Formalism.L2.FormalSeriesBounds
