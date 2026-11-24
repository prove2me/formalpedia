-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Van.mul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:09:39.22112+00:00
-- url     : https://prove2.me/submissions/bb1d4eec-c743-4298-9ae8-14206967a720

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes

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
variable {τ : Type}
namespace Formalism.L2.FormalSeriesBounds
namespace Van
theorem _root_.solution {T : Set τ} {f : MvPowerSeries τ C} (hf : Van T f) (g : MvPowerSeries τ C) :
    Van T (f * g) := by
  intro ν hν
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨a, b⟩ hab
  have hab' : a + b = ν := Finset.HasAntidiagonal.mem_antidiagonal.1 hab
  have h0 : coeff a f = 0 := hf a fun w hw => hν w (by
    rw [← hab', Finsupp.mem_support_iff, Finsupp.add_apply]
    have := Finsupp.mem_support_iff.1 hw
    omega)
  simp [h0]
end Van
end Formalism.L2.FormalSeriesBounds
