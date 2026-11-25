-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.FrobP.valuation_coeff_mul_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:37:46.232983+00:00
-- url     : https://prove2.me/submissions/8ef5eb59-9252-4dc9-a03e-e11d4ee762b4

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FrobSerSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffPowCharFrobenius

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open ValuationNonnegativity
open Formalism.L2.FormalSeriesBounds.FrobP
variable {C : Type} [Field C] {V : VF C}
namespace Formalism.L2.FormalSeriesBounds.FrobP
theorem _root_.solution {f g : PowerSeries C} (hf : ∀ n, V.Ge 0 (PowerSeries.coeff n f))
    (hg : ∀ n, V.Ge 0 (PowerSeries.coeff n g)) : ∀ n, V.Ge 0 (PowerSeries.coeff n (f * g)) := by
  intro n
  unfold VF.Ge at *
  rw [PowerSeries.coeff_mul]
  apply AddValuation.map_le_sum
  intro x _
  rw [AddValuation.map_mul]
  have h1 := hf x.1
  have h2 := hg x.2
  rw [WithTop.coe_zero] at h1 h2 ⊢
  exact add_nonneg h1 h2
end Formalism.L2.FormalSeriesBounds.FrobP
