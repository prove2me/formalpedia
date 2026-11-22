-- Prove2me | solution 1 for DistanceGeometry.schoenberg_hard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:46:59.239667+00:00
-- url     : https://prove2.me/submissions/f8edd1bf-25e4-4054-aed9-cf101152fdc7

module
public import Definitions.Def_LeanPool_DistanceGeometry_Defs
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Definitions.Def_LeanPool_DistanceGeometry_Schoenberg
public import Mathlib.Analysis.Matrix.PosDef
public import Definitions.Def_LeanPool_DistanceGeometry_SchoenbergHard
public import Theorems.Thm_Matrix_PosSemidef_exists_conjTranspose_mul_self_of_rank_le
public import Theorems.Thm_DistanceGeometry_IsPreDistMatrix_hollow
public import Theorems.Thm_DistanceGeometry_IsPreDistMatrix_symm
public import Theorems.Thm_DistanceGeometry_IsSqDistMatrix_hollow
public import Theorems.Thm_DistanceGeometry_IsSqDistMatrix_symm
public import Theorems.Thm_DistanceGeometry_centeredGram_apply
public import Theorems.Thm_DistanceGeometry_sqDistMatrix_apply
attribute [local simp] DistanceGeometry.centeredGram_apply
attribute [local simp] DistanceGeometry.sqDistMatrix_apply



set_option autoImplicit true
@[expose] public section
public section
open Matrix
open scoped RealInnerProductSpace
open DistanceGeometry
open Matrix
open scoped RealInnerProductSpace
variable {n k : ℕ} [NeZero n]
namespace DistanceGeometry
theorem _root_.solution
    {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : IsPreDistMatrix D)
    (hPSD : (centeredGram D).PosSemidef)
    (hrank : (centeredGram D).rank ≤ k) :
    EmbedsIn D k := by
  classical
  set G := centeredGram D with hGdef
  -- rank-controlled factorization `Mᴴ * M = G`
  obtain ⟨M, hM⟩ := hPSD.exists_conjTranspose_mul_self_of_rank_le hrank
  -- points = columns of `M`, viewed in `EuclideanSpace ℝ (Fin k)`
  refine ⟨fun i => (WithLp.toLp 2 (Mᵀ i) : EuclideanSpace ℝ (Fin k)), ?_⟩
  intro i j
  -- inner product of columns `i` and `j` of `M` is `(Mᴴ * M) i j = G i j`
  have hinner : ∀ a b : Fin n,
      ⟪(WithLp.toLp 2 (Mᵀ a) : EuclideanSpace ℝ (Fin k)),
        (WithLp.toLp 2 (Mᵀ b) : EuclideanSpace ℝ (Fin k))⟫ = G a b := by
    intro a b
    -- `⟪col a, col b⟫ = ∑ t, M t a * M t b = (Mᴴ * M) a b = G a b`
    rw [← hM, mul_apply]
    simp only [PiLp.inner_apply, transpose_apply, conjTranspose_apply, star_trivial]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    calc (inner ℝ (M t a) (M t b) : ℝ) = (starRingEnd ℝ) (M t a) * M t b :=
          RCLike.inner_apply' (M t a) (M t b)
      _ = M t a * M t b := by rw [conj_trivial]
  -- reverse polarization: dist² = ⟪v,v⟫ = ⟪xi,xi⟫ - ⟪xi,xj⟫ - ⟪xj,xi⟫ + ⟪xj,xj⟫
  rw [dist_eq_norm, ← real_inner_self_eq_norm_sq, inner_sub_sub_self]
  beta_reduce
  rw [hinner i i, hinner i j, hinner j i, hinner j j]
  simp only [hGdef, centeredGram_apply]
  -- now purely algebraic: use symmetry and hollowness of `D`
  rw [hD.hollow i, hD.hollow j, hD.symm j i]
  ring
end DistanceGeometry
