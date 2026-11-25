-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.InL.rescale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:26:38.454805+00:00
-- url     : https://prove2.me/submissions/fdf10ba9-377f-4f21-8b06-3856d2d5358c

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeOfPowEqOne

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
theorem _root_.solution {l : ℕ} {ζ : C} (hζ : ζ ^ l = 1) {f : PowerSeries C} (hf : InL l f) :
    PowerSeries.rescale ζ f = f := by
  ext m
  rw [PowerSeries.coeff_rescale]
  by_cases hm : l ∣ m
  · obtain ⟨k, rfl⟩ := hm
    rw [pow_mul, hζ, one_pow, one_mul]
  · rw [hf m hm, mul_zero]
end InL
end Formalism.L2.FormalSeriesBounds
