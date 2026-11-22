-- Prove2me | solution 1 for Formalism.HN.PlaceOperatorNorms.cnorm_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:14:09.378236+00:00
-- url     : https://prove2.me/submissions/98145579-42e4-476b-bde0-1b8a8155b441

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_TwistFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_RescaleCovol
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNSlopes
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean

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
open Formalism.HN.PlaceOperatorNorms
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
  {W κ : Type} [AddCommGroup W] [Module K W] [Fintype κ] [DecidableEq κ]
namespace Formalism.HN.PlaceOperatorNorms
theorem _root_.solution (u : κ → ℂ) : Formalism.HermitianLatticesTheory.cnorm u = ‖(WithLp.toLp 2 u : EuclideanSpace ℂ κ)‖ := by
  simp [Formalism.HermitianLatticesTheory.cnorm, EuclideanSpace.norm_eq]
end Formalism.HN.PlaceOperatorNorms
