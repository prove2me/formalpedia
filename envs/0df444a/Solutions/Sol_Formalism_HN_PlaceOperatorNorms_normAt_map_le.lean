-- Prove2me | solution 1 for Formalism.HN.PlaceOperatorNorms.normAt_map_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:02.246022+00:00
-- url     : https://prove2.me/submissions/aa5bb454-ca12-4153-824b-7479710f7042

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
import Theorems.Thm_Formalism_HN_PlaceOperatorNorms_cnorm_eq
import Theorems.Thm_Formalism_HN_PlaceOperatorNorms_fcoord_map

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
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (b' : Basis κ K W)
    (X' : InfinitePlace K → Matrix κ κ ℂ) (hX : ∀ v, IsUnit (X v).det) (v : InfinitePlace K)
    (φ : V →ₗ[K] W) (x : V) :
    Formalism.HermitianLatticesTheory.normAt b' X' v (φ x) ≤ opNormAt b X b' X' v φ * Formalism.HermitianLatticesTheory.normAt b X v x := by
  rw [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.normAt, fcoord_map b X b' X' hX v φ x, cnorm_eq, cnorm_eq, opNormAt]
  have := (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
    ((X' v)⁻¹ * (LinearMap.toMatrix b b' φ).map v.embedding * X v))).le_opNorm
      (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v x))
  convert this using 1
  all_goals first
    | rfl
    | simp [Matrix.toEuclideanLin_apply]
    | (congr 1; simp [Matrix.toEuclideanLin_apply])
end Formalism.HN.PlaceOperatorNorms
