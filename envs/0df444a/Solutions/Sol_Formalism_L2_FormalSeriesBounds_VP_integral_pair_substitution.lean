-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.integral_pair_substitution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:37:10.381452+00:00
-- url     : https://prove2.me/submissions/17c37c1c-8e73-455d-9d43-4a59649ba7f9

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
theorem _root_.solution {a b : Fin dd → MvPowerSeries τ C} (ha : ∀ i, IntS V (a i)) (hb : ∀ i, IntS V (b i))
    (q : Fin 2 × Fin dd) : IntS V (P2 a b q) := by
  unfold P2
  split_ifs
  exacts [ha _, hb _]
end Formalism.L2.FormalSeriesBounds.VP
