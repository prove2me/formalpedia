-- Prove2me | solution 1 for Formalism.IndefR.LocBrg.newton_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:47.850527+00:00
-- url     : https://prove2.me/submissions/e37c10f6-c6db-4490-bb7c-02ffe766b27c

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LocalNormSurjectivity_FinNormSurj
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LocalNormSurjectivity_WittHS
import Theorems.Thm_Formalism_IndefR_LocBrg_pow_small
import Theorems.Thm_Formalism_IndefR_LocBrg_pow_anti
import Theorems.Thm_Formalism_IndefR_LocBrg_newton_cauchy_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.LocBrg
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
local notation "vv" => (Valued.v : Valuation L (WithZero (Multiplicative ℤ)))
variable (u : L)
namespace Formalism.IndefR.LocBrg
theorem _root_.solution (h2 : vv (2 : L) = 1) (hu : vv (u - 1) < 1) : CauchySeq (newtonSq u) := by
  rw [(Valued.hasBasis_uniformity L (WithZero (Multiplicative ℤ))).cauchySeq_iff]
  intro γ _
  obtain ⟨N, hN⟩ := pow_small hu (Units.mk0 _ (MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ))
  rw [Units.val_mk0] at hN
  refine ⟨N, fun m hm n hn => ?_⟩
  show Valued.v.restrict (newtonSq u n - newtonSq u m) < (γ : _)
  rw [Valuation.restrict_lt_iff_lt_embedding]
  rcases le_total m n with hmn | hnm
  · calc vv (newtonSq u n - newtonSq u m) ≤ vv (u - 1) ^ (m + 1) := newton_cauchy_bound u h2 hu m n hmn
      _ ≤ vv (u - 1) ^ N := pow_anti hu.le (by omega)
      _ < _ := hN
  · rw [Valuation.map_sub_swap]
    calc vv (newtonSq u m - newtonSq u n) ≤ vv (u - 1) ^ (n + 1) := newton_cauchy_bound u h2 hu n m hnm
      _ ≤ vv (u - 1) ^ N := pow_anti hu.le (by omega)
      _ < _ := hN
end Formalism.IndefR.LocBrg
