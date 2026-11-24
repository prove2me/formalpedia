-- Prove2me | solution 1 for Formalism.L2.Geo.Rec.DualLatticeEmbeddings.inner_mkE_fc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:02:21.521262+00:00
-- url     : https://prove2.me/submissions/2d34d30f-9bea-4482-b9dc-f61a73538ff1

import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_GelfandTransference_EnergyIdentity
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_RealizationNorms_ExistsStarMulSelf
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_RealizationNorms_SumUliftFinsetFinTwoExpand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.InfinitePlace Module Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.Rec Formalism.L2.Geo.Rec.DualLatticeEmbeddings
variable {K : Type} [Field K] [NumberField K] {n : ℕ}
variable [StarRing K]
namespace Formalism.L2.Geo.Rec.DualLatticeEmbeddings
theorem _root_.solution (Xf : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hXf : ∀ v, IsUnit (Xf v).det)
    (x ξ : Fin n → K) (v : InfinitePlace K) :
    ∑ i, (star (fc Xf v x i) * ((2 : ℂ) • ((Xf v)ᴴ *ᵥ (fun i => star (v.embedding (ξ i))))) i).re =
      2 * (v.embedding (∑ i, ξ i * x i)).re := by
  have hinv : Xf v * (Xf v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (hXf v)
  have key : star (fc Xf v x) ⬝ᵥ ((Xf v)ᴴ *ᵥ fun i => star (v.embedding (ξ i))) =
      star (v.embedding (∑ i, ξ i * x i)) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
    unfold fc
    rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    simp [dotProduct, map_sum, star_sum, map_mul, mul_comm]
  have hsum : ∑ i, (star (fc Xf v x i) * ((2 : ℂ) • ((Xf v)ᴴ *ᵥ fun i => star (v.embedding (ξ i)))) i).re =
      2 * (star (fc Xf v x) ⬝ᵥ ((Xf v)ᴴ *ᵥ fun i => star (v.embedding (ξ i)))).re := by
    simp only [dotProduct, Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Complex.mul_re]
    ring
  rw [hsum, key, Complex.star_def, Complex.conj_re]
end Formalism.L2.Geo.Rec.DualLatticeEmbeddings
