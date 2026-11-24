-- Prove2me | solution 1 for Formalism.HN.PlaceOperatorNorms.opNormAt_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:14.888804+00:00
-- url     : https://prove2.me/submissions/1ecf6a90-6ccb-4e47-8da5-1d80983290e1

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
    (X' : InfinitePlace K → Matrix κ κ ℂ) (hX' : ∀ v, IsUnit (X' v).det) (c : InfinitePlace K → ℝ)
    (hc : ∀ v, 0 < c v) (v : InfinitePlace K) (φ : V →ₗ[K] W) :
    opNormAt b X b' (fun w => ((c w : ℂ)) • X' w) v φ = (c v)⁻¹ * opNormAt b X b' X' v φ := by
  have hc0 : ((c v : ℂ)) ≠ 0 := by exact_mod_cast (hc v).ne'
  have hi : ((c v : ℂ) • X' v)⁻¹ = ((c v : ℂ))⁻¹ • (X' v)⁻¹ := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul,
      Matrix.nonsing_inv_mul _ (hX' v)]
  simp only [opNormAt, hi, Matrix.smul_mul, map_smul, norm_smul]
  first
    | rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (hc v).le]
    | simp [norm_inv, abs_of_pos (hc v)]
end Formalism.HN.PlaceOperatorNorms
