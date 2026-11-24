-- Prove2me | solution 1 for Formalism.HN.Rerealization.covol_eq_exp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:32.672968+00:00
-- url     : https://prove2.me/submissions/78bc12b0-0778-411c-8a51-de974c5d72ce

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Theorems.Thm_Formalism_F_covol_pos


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
open Formalism.HN.Rerealization
variable {R V E E₂ : Type*} [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup E₂]
  [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
namespace Formalism.HN.Rerealization
theorem _root_.solution {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    [FiniteDimensional ℝ E'] (L : Submodule ℤ E') (h : DiscreteTopology L) :
    Formalism.F.covol L = Real.exp (- Formalism.F.deg L) := by
  haveI := h
  rw [Formalism.F.deg, neg_neg, Real.exp_log (Formalism.F.covol_pos L)]
end Formalism.HN.Rerealization
