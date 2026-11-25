-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.le_v_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:27:03.007092+00:00
-- url     : https://prove2.me/submissions/6abc9f06-860e-4148-9f51-a2cfd563b8f7

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_HostTraceIdentity
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieDesc

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
variable {C : Type} [Field C] {V : VF C}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (x : WithTop ℝ) {m : ℕ} (z : Fin m → C) (h : ∀ i, x ≤ V.v (z i)) : x ≤ V.v (∑ i, z i) := by
  refine Finset.sum_induction z (fun w => x ≤ V.v w)
    (fun a b ha hb => le_trans (le_min ha hb) (V.v.map_add a b)) ?_ (fun i _ => h i)
  rw [AddValuation.map_zero]
  exact le_top
end Formalism.L2.FormalSeriesBounds
