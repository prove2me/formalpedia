-- Prove2me | solution 1 for Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.opNormAt_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:30.918313+00:00
-- url     : https://prove2.me/submissions/50c81bbd-67e4-4e21-8cab-ae064ce19efb

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_MuMaxMinkowski
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GoodBadCut
import Theorems.Thm_Formalism_ExtensionFiltration_HermitianIdempotentFrameLemmas_norm_herm_idem_le
import Theorems.Thm_Formalism_ExtensionFiltration_HermitianIdempotentFrameLemmas_frameMat_herm
import Theorems.Thm_Formalism_ExtensionFiltration_HermitianIdempotentFrameLemmas_frameMat_idem

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
open Formalism Formalism.ExtensionFiltration
open Formalism.HN
open Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
namespace Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (e : V →ₗ[K] V) (g : ℕ) (v : InfinitePlace K) (hee : e ∘ₗ e = e)
    (hsa : ∀ x y, Formalism.HermitianLatticesTheory.majAt b X v (e x) y = Formalism.HermitianLatticesTheory.majAt b X v x (e y)) :
    opNormAt b X b X v ((g : K) • (LinearMap.id - e)) ≤ (g : ℝ) := by
  have hH := frameMat_herm b X hX e v hsa
  have hI := frameMat_idem b X hX e v hee
  have hXinv : (X v)⁻¹ * X v = 1 := Matrix.nonsing_inv_mul _ (hX v)
  set F := (X v)⁻¹ * (LinearMap.toMatrix b b e).map v.embedding * X v with hF
  have h1 : LinearMap.toMatrix b b ((g : K) • (LinearMap.id - e)) =
      g • (1 - LinearMap.toMatrix b b e) := by
    rw [Nat.cast_smul_eq_nsmul, map_nsmul, map_sub, LinearMap.toMatrix_id]
  have h2 : (g • (1 - LinearMap.toMatrix b b e)).map v.embedding =
      g • (1 - (LinearMap.toMatrix b b e).map v.embedding) := by
    have h3 := map_nsmul (v.embedding.mapMatrix) g (1 - LinearMap.toMatrix b b e)
    rw [map_sub, map_one] at h3
    exact h3
  have hmat : (X v)⁻¹ * (LinearMap.toMatrix b b ((g : K) • (LinearMap.id - e))).map v.embedding * X v =
      g • (1 - F) := by
    rw [h1, h2, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hXinv, hF]
  have hH' : (1 - F).IsHermitian := by
    unfold Matrix.IsHermitian at hH ⊢
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hH]
  have hI' : (1 - F) * (1 - F) = 1 - F := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hI]
    abel
  unfold opNormAt
  rw [hmat]
  apply ContinuousLinearMap.opNorm_le_bound _ (Nat.cast_nonneg g)
  intro z
  have hz := norm_herm_idem_le (1 - F) hH' hI' z
  have happ : (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (g • (1 - F)))) z =
      g • Matrix.toEuclideanLin (1 - F) z := by
    rw [LinearMap.coe_toContinuousLinearMap', map_nsmul, LinearMap.smul_apply]
  rw [happ, ← Nat.cast_smul_eq_nsmul ℂ, norm_smul]
  have hgn : ‖(g : ℂ)‖ = g := by simp
  rw [hgn]
  exact mul_le_mul_of_nonneg_left hz (Nat.cast_nonneg g)
end Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas
