-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.constantCoeff_triple_substitution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:52:42.521548+00:00
-- url     : https://prove2.me/submissions/0652d726-866e-46c9-87fd-9ec9e6fefbbb

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValU
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstantCoeffTripleSubstitution

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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open Formalism.L2.FormalSeriesBounds.VP
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ : Type}
namespace Formalism.L2.FormalSeriesBounds.VP
theorem _root_.solution {a b c : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) (hc : ∀ i, MvPowerSeries.constantCoeff (c i) = 0)
    (q : Fin 3 × Fin dd) : MvPowerSeries.constantCoeff (P3 a b c q) = 0 := by
  unfold P3
  split_ifs
  exacts [ha _, hb _, hc _]
end Formalism.L2.FormalSeriesBounds.VP
