-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.intS_ps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:48:03.397934+00:00
-- url     : https://prove2.me/submissions/5d6481bb-ec98-4ce6-9111-bbc83cb781c8

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartAdd

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
variable {V : VF C} {τ : Type}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {f : PowerSeries C} : IntS V f ↔ ∀ n, V.Ge 0 (PowerSeries.coeff n f) := by
  constructor
  · intro h n
    exact h (Finsupp.single () n)
  · intro h μ
    have hμ : μ = Finsupp.single () (μ ()) := by
      ext
      simp [Finsupp.single_apply]
    rw [hμ]
    exact h (μ ())
end Formalism.L2.FormalSeriesBounds
