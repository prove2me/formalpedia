-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.inL_of_rescale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:26:34.64189+00:00
-- url     : https://prove2.me/submissions/425a4dea-b0e7-4ff2-8811-e43a44ca1b90

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
theorem _root_.solution {l : ℕ} {ζ : C} (hζ : IsPrimitiveRoot ζ l) {f : PowerSeries C}
    (h : PowerSeries.rescale ζ f = f) : InL l f := by
  intro m hm
  have h1 := congrArg (PowerSeries.coeff m) h
  rw [PowerSeries.coeff_rescale] at h1
  have h2 : ζ ^ m ≠ 1 := fun e => hm ((hζ.pow_eq_one_iff_dvd m).mp e)
  have h3 : (ζ ^ m - 1) * PowerSeries.coeff m f = 0 := by
    rw [sub_mul, h1, one_mul, sub_self]
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact absurd (sub_eq_zero.mp h4) h2
  · exact h4
end Formalism.L2.FormalSeriesBounds
