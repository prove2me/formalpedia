-- Prove2me | solution 1 for Formalism.HN.PlaceOperatorNorms.opNormAt_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:30:35.027306+00:00
-- url     : https://prove2.me/submissions/4ab17219-060a-46dd-aa5b-aba68e7a3b6e

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
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (b' : Basis κ K W)
    (X' : InfinitePlace K → Matrix κ κ ℂ) (hX : ∀ v, IsUnit (X v).det)
    (hX' : ∀ v, IsUnit (X' v).det) (v : InfinitePlace K) (φ : V →ₗ[K] W) (hφ : φ ≠ 0) :
    0 < opNormAt b X b' X' v φ := by
  rw [opNormAt, norm_pos_iff]
  intro h0
  apply hφ
  have hA := (Matrix.toEuclideanLin.map_eq_zero_iff).mp
    ((LinearMap.toContinuousLinearMap.map_eq_zero_iff).mp h0)
  have hΦ : (LinearMap.toMatrix b b' φ).map v.embedding = 0 := by
    have e : (LinearMap.toMatrix b b' φ).map v.embedding =
        X' v * ((X' v)⁻¹ * (LinearMap.toMatrix b b' φ).map v.embedding * X v) * (X v)⁻¹ := by
      simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hX v), Matrix.mul_one]
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hX' v), Matrix.one_mul]
    rw [e, hA, Matrix.mul_zero, Matrix.zero_mul]
  have hM : LinearMap.toMatrix b b' φ = 0 := by
    ext i j
    have := congrFun (congrFun hΦ i) j
    simpa using this
  exact (LinearMap.toMatrix b b').map_eq_zero_iff.mp hM
end Formalism.HN.PlaceOperatorNorms
