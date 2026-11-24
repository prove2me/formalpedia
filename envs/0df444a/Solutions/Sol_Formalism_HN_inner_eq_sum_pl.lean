-- Prove2me | solution 1 for Formalism.HN.inner_eq_sum_pl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:28.955372+00:00
-- url     : https://prove2.me/submissions/c643ffe8-17d1-4f99-8b52-48f9c5f00fc6

import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_GramBlock
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_RescaleCovol

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HN
namespace Formalism.HN
theorem _root_.solution {P ι : Type*} [Fintype P] [Fintype ι]
    (x y : EuclideanSpace ℝ (P × ι × Fin 2)) :
    inner ℝ x y = ∑ p, x p * y p := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [mul_comm]
end Formalism.HN
