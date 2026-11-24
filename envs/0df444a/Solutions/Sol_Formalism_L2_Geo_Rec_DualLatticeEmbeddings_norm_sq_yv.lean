-- Prove2me | solution 1 for Formalism.L2.Geo.Rec.DualLatticeEmbeddings.norm_sq_yv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:22:05.023307+00:00
-- url     : https://prove2.me/submissions/cfc4f5c7-d9fb-4e3f-b70d-8427940a3b1f

import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_GelfandTransference_EnergyIdentity
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_RealizationNorms_ExistsStarMulSelf
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_RealizationNorms_SumUliftFinsetFinTwoExpand
import Theorems.Thm_Formalism_L2_Geo_Rec_DualLatticeEmbeddings_norm_sq_mkE

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
open NumberField NumberField.InfinitePlace Module Matrix
noncomputable section
open NumberField NumberField.InfinitePlace Module Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.Rec Formalism.L2.Geo.Rec.DualLatticeEmbeddings
variable {K : Type} [Field K] [NumberField K] {n : ℕ} [StarRing K] [IsTotallyComplex K]
namespace Formalism.L2.Geo.Rec.DualLatticeEmbeddings
theorem _root_.solution (cj : K → K) (hσ : ∀ (v : InfinitePlace K) z, v.embedding (cj z) = star (v.embedding z))
    (A : Matrix (Fin n) (Fin n) K) (Xf : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    (hfr : ∀ v, Xf v * (Xf v)ᴴ = A.map v.embedding) (ξ : Fin n → K) :
    ‖yv Xf ξ‖ ^ 2 = 4 * ∑ v : InfinitePlace K, (v.embedding (∑ i, ∑ k, ξ i * A i k * cj (ξ k))).re := by
  have hre : ∀ u : Fin n → ℂ, ∑ i, ‖u i‖ ^ 2 = (star u ⬝ᵥ u).re := by
    intro u
    simp only [dotProduct, Complex.re_sum, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.mul_re]
  have hsm : ∀ (u : Fin n → ℂ) (i : Fin n), ‖((2 : ℂ) • u) i‖ ^ 2 = 4 * ‖u i‖ ^ 2 := by
    intro u i
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
    norm_num
  unfold yv
  rw [norm_sq_mkE, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp_rw [hsm]
  rw [← Finset.mul_sum, hre]
  congr 2
  rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, hfr v]
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, map_sum, map_mul, hσ, Pi.star_apply, star_star,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring
end Formalism.L2.Geo.Rec.DualLatticeEmbeddings
