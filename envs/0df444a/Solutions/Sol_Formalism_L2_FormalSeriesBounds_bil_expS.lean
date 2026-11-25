-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.bil_expS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:08:19.356114+00:00
-- url     : https://prove2.me/submissions/4d79c541-afcc-4cd6-9c84-45887cdff046

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStab
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_exchangeTwo_self_eq_one
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_elementary_pair_support
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_expS_bil
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ne01

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
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {f : PS C 2 dd} (hf : Van (Tg dd 0) f) (w v : Fin dd → C) : bil (FB.expS C f) w v = bil f w v := by
  unfold bil
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [coeff_expS_bil hf (E2 ((0 : Fin 2), i) ((1 : Fin 2), j)) ((0 : Fin 2), i) ?_ (le_of_eq (exchangeTwo_self_eq_one (ne01 i j))) ?_]
  · intro s hs h0
    rcases elementary_pair_support h0 with e | e
    · exact e
    · have h1 : s.1 = 0 := hs
      rw [e] at h1
      have h2 : (1 : Fin 2) = 0 := h1
      exact absurd h2 (by decide)
  · intro h0
    have := exchangeTwo_self_eq_one (ne01 i j)
    rw [h0] at this
    exact absurd this (by simp)
end Formalism.L2.FormalSeriesBounds
