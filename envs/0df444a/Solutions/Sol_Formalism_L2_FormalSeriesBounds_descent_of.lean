-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.descent_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:16:15.643072+00:00
-- url     : https://prove2.me/submissions/6c026a9d-91ca-4637-b358-3c8476ffaa92

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_HostTraceIdentity
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieDesc
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_nuLocC_le_nval
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_le_v_sum

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
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable (Xo c)
variable {Xo c}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (h1 : NabMapSt Xo c) (h2 : DescSpanSt Xo c) (h3 : NvalEqSt) : DescentSt Xo c := by
  intro T io y C3 C _ _ V ι hι k Y hY a n
  unfold FBChart.nuPlE
  refine le_iInf₂ fun x hx => ?_
  obtain ⟨P, hP, f, hf, rfl⟩ := hx
  obtain ⟨m, r, Pi, fi, hr, hPi, hfi, heq⟩ := h2 T io y C3 C V ι hι k Y hY a n P hP f hf
  have hz : ∀ i, nuLocC C3 (eOf T V) k a n ≤ (WithBot.some (V.v (Y.nab (chartLetterSystem C3 V ι a) n
      (MvPowerSeries.map ι (fi i)) (MvPolynomial.map ι (Pi i)))) : WithBot (WithTop ℝ)) := by
    intro i
    rw [h1 T io y C3 C V ι k Y hY a n (fi i) (Pi i), h3 T C V ι hι]
    exact nuLocC_le_nval C3 (eOf T V) k a n (Pi i) (hPi i) (fi i) (hfi i)
  rw [heq]
  generalize nuLocC C3 (eOf T V) k a n = ν at hz ⊢
  rcases ν with _ | w
  · exact bot_le
  · refine WithBot.coe_le_coe.mpr (le_v_sum w _ fun i => ?_)
    have hzi := WithBot.coe_le_coe.mp (hz i)
    rw [AddValuation.map_mul]
    calc w = 0 + w := (zero_add w).symm
      _ ≤ V.v (r i) + _ := add_le_add (hr i) hzi
end Formalism.L2.FormalSeriesBounds
