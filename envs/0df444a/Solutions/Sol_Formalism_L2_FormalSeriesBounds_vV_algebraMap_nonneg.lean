-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.vV_algebraMap_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:26:37.253491+00:00
-- url     : https://prove2.me/submissions/e35cc4da-f66c-49e4-b69b-3631fc95aef4

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCuts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePEmbIntSt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.Pj
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (T : CDVR) (t : T.V) : 0 ≤ vV T.V (algebraMap T.V T.Fr t) := by
  have hle := (IsDiscreteValuationRing.maximalIdeal T.V).valuation_le_one (K := T.Fr) t
  unfold vV valV
  generalize (IsDedekindDomain.HeightOneSpectrum.valuation T.Fr
    (IsDiscreteValuationRing.maximalIdeal T.V)) (algebraMap T.V T.Fr t) = y at hle ⊢
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · obtain ⟨a, rfl⟩ := WithZero.ne_zero_iff_exists.1 hy
    have ha : a ≤ 1 := WithZero.coe_le_one.1 hle
    have hlog : WithZero.log (a : WithZero (Multiplicative ℤ)) = Multiplicative.toAdd a := rfl
    rw [hlog, neg_nonneg]
    exact ha
end Formalism.L2.FormalSeriesBounds
