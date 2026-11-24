-- Prove2me | solution 1 for Formalism.HN.QuotientRealization.inner_sum_psi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:18.872092+00:00
-- url     : https://prove2.me/submissions/ea94ba9c-33b9-4513-87b0-e7a5cd3d8552

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_QuotRealize
import Theorems.Thm_Formalism_HN_QuotientRealization_inner_psi_psi

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
variable {P ι : Type*} [Fintype P] [DecidableEq P] [Fintype ι]
namespace Formalism.HN.QuotientRealization
theorem _root_.solution (y z : P → ι → ℂ) :
    inner ℝ (∑ u, PlaceDecomposition.psi u (y u)) (∑ v, PlaceDecomposition.psi (ι := ι) v (z v)) =
      ∑ v, (inner ℂ (WithLp.toLp 2 (y v) : EuclideanSpace ℂ ι) (WithLp.toLp 2 (z v))).re := by
  simp [sum_inner, inner_sum, inner_psi_psi]
end Formalism.HN.QuotientRealization
