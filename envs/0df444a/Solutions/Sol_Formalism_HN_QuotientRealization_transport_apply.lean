-- Prove2me | solution 1 for Formalism.HN.QuotientRealization.transport_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:24.292357+00:00
-- url     : https://prove2.me/submissions/3b09f0cb-5bc6-435a-9f7a-9f62d9386da0

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_QuotRealize

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.QuotientRealization
variable {E F M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [AddCommGroup M]
namespace Formalism.HN.QuotientRealization
theorem _root_.solution (f : M →+ E) (g : M →+ F) (L1 : Submodule ℤ E) (L2 : Submodule ℤ F)
    (h1 : ∀ y, y ∈ L1 ↔ ∃ m, f m = y) (h2 : ∀ y, y ∈ L2 ↔ ∃ m, g m = y)
    (hn : ∀ m, ‖f m‖ = ‖g m‖) (y : L1) (m : M) (hm : f m = y) :
    ((transport f g L1 L2 h1 h2 hn y : L2) : F) = g m := by
  show g ((h1 y).1 y.2).choose = g m
  exact eq_of_norm_eq f g hn (((h1 y).1 y.2).choose_spec.trans hm.symm)
end Formalism.HN.QuotientRealization
